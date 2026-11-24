/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.MellinTransform.Sawtooth
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.EulerMaclaurin

/-!
# Right-half-plane bounds for `riemannZeta`

The first-order Euler–Maclaurin formula of
`TauCeti.NumberTheory.LSeries.RiemannZeta.EulerMaclaurin` writes `ζ(s)`, for `Re s > 0`, `s ≠ 1`,
as a finite sum, a polar term and the tail `s ∫_a^∞ B₁({t}) t^(-s-1) dt` of the sawtooth
`B₁({t}) = {t} - 1/2`, which is bounded by `1/2`. The tail bound gives the truncation error
`‖s‖ a^(-Re s)/(2 Re s)` at every cut point `a > 0`, and at `a = 1` the bound
`‖riemannZeta₀ s - 1/2‖ ≤ ‖s‖/(2 Re s)` on all of `Re s > 0`. Hence
`‖ζ(z)‖ ≤ 1/2 + 1/‖z - 1‖ + ‖z‖/(2 Re z)` for `z ≠ 1`, and the weaker vertical-line bounds

`‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s`   and   `‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s`

for all `Re s > 0` (including at `s = 1`, where Mathlib's junk value `(γ - log(4π)) / 2` has norm
strictly less than `2`). On the discs `‖z - (3/2 + it)‖ ≤ 1` with `|t| ≥ 2` the bound is at most
`4 + |t|`: the input that Borel–Carathéodory arguments near the line `Re s = 1` take. On the real
axis, the fractional-part formula `ζ(σ) = 1 + (σ - 1)⁻¹ - σ ∫_1^∞ {t} t^(-σ-1) dt` and
`0 ≤ {t} < 1` give `1/(σ - 1) < ζ(σ) < 1 + 1/(σ - 1)` for real `σ > 0`, `σ ≠ 1`.

## Main results

* `TauCeti.norm_riemannZeta_sub_sum_sawtooth_le`, with its cases
  `TauCeti.norm_riemannZeta_sub_sum_sawtooth_natCast_le` and
  `TauCeti.norm_riemannZeta_sub_sum_sawtooth_natCast_add_half_le`: the truncation error of the
  first-order Euler–Maclaurin formula at a cut point `a > 0`, an integer and a half-integer.
* `TauCeti.norm_riemannZeta₀_sub_one_half_le`: `‖riemannZeta₀ s - 1/2‖ ≤ ‖s‖/(2 Re s)` on
  `Re s > 0`.
* `TauCeti.norm_riemannZeta_le_one_half_add_inv_add_div`,
  `TauCeti.norm_riemannZeta_le_three_halves_add_norm` and `TauCeti.norm_riemannZeta_le_linear`:
  linear bounds in the right half-plane and on the discs about `3/2 + it`.
* `TauCeti.norm_riemannZeta₀_le_one_add_norm_div_re` and `TauCeti.norm_riemannZeta_le_of_re_pos`:
  `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s` and `‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s` on
  `Re s > 0`.
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
  have h := norm_riemannZeta_sub_sum_sawtooth_le (a := (N : ℝ) + 1 / 2) (by positivity) hs hs₁
  simpa [bernoulliFun_one] using h

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
  have htri : ‖(1 / 2 : ℂ) + (z - 1)⁻¹ + (riemannZeta₀ z - 1 / 2)‖ ≤
      ‖(1 / 2 : ℂ)‖ + ‖(z - 1)⁻¹‖ + ‖riemannZeta₀ z - 1 / 2‖ := norm_add₃_le
  linarith [norm_riemannZeta₀_sub_one_half_le hz]

/-- On the open right half-plane `Re s > 0`, `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s`, a weakening of
`TauCeti.norm_riemannZeta₀_sub_one_half_le`. -/
theorem norm_riemannZeta₀_le_one_add_norm_div_re {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re := by
  have h := norm_sub_norm_le (riemannZeta₀ s) (1 / 2)
  have hdiv : ‖s‖ / (2 * s.re) ≤ ‖s‖ / s.re :=
    div_le_div_of_nonneg_left (norm_nonneg s) hs (by linarith)
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  linarith [norm_riemannZeta₀_sub_one_half_le hs]

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
  · have h := norm_riemannZeta_le_one_half_add_inv_add_div hs hs1
    have hdiv : ‖s‖ / (2 * s.re) ≤ ‖s‖ / s.re :=
      div_le_div_of_nonneg_left (norm_nonneg s) hs (by linarith)
    rw [one_div ‖s - 1‖] at h
    linarith

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
    rw [hzw]
    have htri : ‖w + 3 / 2 + (t : ℂ) * I‖ ≤ ‖w‖ + ‖(3 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add₃_le
    linarith
  linarith [norm_riemannZeta_le_three_halves_add_norm hz_re hpole]

/-! ### Comparison with `1/(σ - 1)` on the real axis -/

/-- **The lower bound by the pole.** For real `σ > 0`, `σ ≠ 1`, `1/(σ - 1) < Re ζ(σ)`. -/
theorem one_div_sub_one_lt_riemannZeta_re {σ : ℝ} (hσ0 : 0 < σ) (hσ₁ : σ ≠ 1) :
    1 / (σ - 1) < (riemannZeta σ).re := by
  have hint_f := integrableOn_rpow_mul_fract (by linarith : -1 - σ < -1) one_pos
  have hint_r : IntegrableOn (fun t : ℝ ↦ t ^ (-1 - σ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hpos : 0 < ∫ t in Set.Ioi (1 : ℝ), (t ^ (-1 - σ) - t ^ (-1 - σ) * Int.fract t) := by
    refine setIntegral_pos_of_ae_pos (by simp) (hint_r.sub hint_f) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
    have hp : 0 < t ^ (-1 - σ) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith [Int.fract_lt_one t]
  have hr : ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) = 1 / σ := by
    have hexp : -1 - σ + 1 = -σ := by ring
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, hexp, neg_div_neg_eq]
  rw [integral_sub hint_r hint_f, hr] at hpos
  have hmul : σ * ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * Int.fract t < 1 := by
    have := mul_lt_mul_of_pos_left hpos hσ0
    rw [mul_sub, mul_one_div_cancel hσ0.ne'] at this
    linarith
  rw [riemannZeta_re_eq_one_add_inv_sub_mul_integral hσ0 hσ₁, one_div]
  linarith

/-- **The upper bound by the pole.** For real `σ > 0`, `σ ≠ 1`, `Re ζ(σ) < 1 + 1/(σ - 1)`. -/
theorem riemannZeta_re_lt_one_add_one_div_sub_one {σ : ℝ} (hσ0 : 0 < σ) (hσ₁ : σ ≠ 1) :
    (riemannZeta σ).re < 1 + 1 / (σ - 1) := by
  have hint := integrableOn_rpow_mul_fract (by linarith : -1 - σ < -1) one_pos
  have hpos : 0 < ∫ t in Set.Ioi (1 : ℝ), t ^ (-1 - σ) * Int.fract t := by
    refine setIntegral_pos_of_ae_pos (by simp) hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae ((Set.countable_range (Int.cast : ℤ → ℝ)).ae_notMem volume)]
      with t (ht : 1 < t) htZ
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      ((Int.fract_nonneg t).lt_of_ne (Int.fract_ne_zero_iff.mpr htZ).symm)
  rw [riemannZeta_re_eq_one_add_inv_sub_mul_integral hσ0 hσ₁, one_div]
  linarith [mul_pos hσ0 hpos]

/-- On `1 < Re s`, `‖ζ(s)‖ < 1 + 1/(Re s - 1)`. -/
theorem norm_riemannZeta_lt_one_add_one_div_sub_one {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ < 1 + 1 / (s.re - 1) :=
  (norm_riemannZeta_le hs).trans_lt
    (riemannZeta_re_lt_one_add_one_div_sub_one (zero_lt_one.trans hs) (by linarith : s.re ≠ 1))

end TauCeti
