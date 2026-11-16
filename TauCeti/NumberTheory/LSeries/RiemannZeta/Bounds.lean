/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.RiemannZeta.Sawtooth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.NumberTheory.LSeries.Positivity
import TauCeti.NumberTheory.LSeries.RiemannZeta

/-!
# Explicit right-half-plane and real-axis bounds for the Riemann zeta function

Combining the first-order Euler–Maclaurin continuation in
`TauCeti.NumberTheory.LSeries.RiemannZeta.Sawtooth` with the upper-tail norm estimate
`‖∫ t in Ioi a, B₁(fract t) * t ^ (-(s + 1))‖ ≤ a ^ (-re s) / (2 * re s)` yields unconditional,
fully explicit truncation and growth bounds for `riemannZeta` and `riemannZeta₀` across the open
right half-plane `0 < re s`:

* **Euler–Maclaurin truncation bounds:** at any positive cutoff `0 < a` (and in particular at
  integer cutoffs `1 ≤ N` and midpoint cutoffs `N + 1 / 2`), the difference between `ζ(s)` and its
  Euler–Maclaurin main terms has norm at most `‖s‖ * a ^ (-re s) / (2 * re s)`.
* **Bounds on `riemannZeta₀` and linear growth on `0 < re s`:** at unit cutoff `a = 1`,
  `‖riemannZeta₀ s - 1 / 2‖ ≤ ‖s‖ / (2 * re s)` for all `0 < re s` (including `s = 1`), giving
  `‖ζ(z)‖ ≤ 1 / 2 + 1 / ‖z - 1‖ + ‖z‖ / (2 * re z)` away from the pole. On the region
  `1 / 2 ≤ re z`, `1 ≤ |im z|` this simplifies to `‖ζ(z)‖ ≤ 3 / 2 + ‖z‖`, and on every closed
  disc `closedBall (3 / 2 + t * I) 1` with `2 ≤ |t|` (used as Borel–Carathéodory input near the
  critical strip) it yields `‖ζ(z)‖ ≤ 4 + |t|`.
* **Real-axis `(1, ∞)` comparison and Dirichlet majorant:** for real `σ > 1`, `Re ζ(σ)` satisfies
  `1 < Re ζ(σ)` and `1 / (σ - 1) < Re ζ(σ) < 1 + 1 / (σ - 1)` and is strictly antitone on `(1, ∞)`.
  By the nonnegative-coefficient Dirichlet majorant in `TauCeti.NumberTheory.LSeries.Positivity`,
  `‖ζ(s)‖ ≤ Re ζ(re s) < 1 + 1 / (re s - 1)` throughout `1 < re s`.

## Main results

* `TauCeti.norm_riemannZeta_sub_sum_sawtooth_le`,
  `TauCeti.norm_riemannZeta_sub_sum_nat_sawtooth_le`,
  `TauCeti.norm_riemannZeta_sub_sum_half_sawtooth_le`: explicit sawtooth truncation error bounds on
  `0 < re s`, `s ≠ 1`.
* `TauCeti.norm_riemannZeta₀_sub_one_half_le`, `TauCeti.norm_riemannZeta₀_sub_one_le`: explicit
  bounds on `riemannZeta₀ s` throughout `0 < re s`.
* `TauCeti.norm_riemannZeta_le_one_half_add_inv_add_div`,
  `TauCeti.norm_riemannZeta_le_three_halves_add_norm`,
  `TauCeti.norm_riemannZeta_le_linear`,
  `TauCeti.norm_riemannZeta_le_of_mem_closedBall`: explicit linear upper bounds on `‖ζ(z)‖` in the
  right half-plane and on unit discs centered at `3 / 2 + t * I`.
* `TauCeti.one_lt_riemannZeta_re`, `TauCeti.strictAntiOn_riemannZeta_re`,
  `TauCeti.one_div_sub_one_lt_riemannZeta_re`,
  `TauCeti.riemannZeta_re_lt_one_add_one_div_sub_one`,
  `TauCeti.norm_riemannZeta_le_riemannZeta_re`,
  `TauCeti.norm_riemannZeta_lt_one_add_one_div_sub_one`: real-axis `(1, ∞)` positivity, strict
  antitonicity, Laurent-type two-sided comparison, and half-plane majorants on `1 < re s`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function* (2nd ed., rev. D. R. Heath-Brown),
  §§2.1, 3.5.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, §6.1.
* O. Ramaré, *Excursions in Multiplicative Number Theory*, Chapter 5.
-/

public section

open Complex Finset MeasureTheory Set
open scoped ComplexOrder

namespace TauCeti

/-! ### Explicit Euler–Maclaurin truncation bounds on `0 < re s` -/

/-- **Explicit sawtooth Euler–Maclaurin truncation bound.** For `0 < re s`, `s ≠ 1`, and any
positive real cutoff `0 < a`, the remainder after the finite sum up to `⌊a⌋₊`, the polar term
`a ^ (1 - s) / (s - 1)`, and the boundary Bernoulli term has norm at most
`‖s‖ * a ^ (-re s) / (2 * re s)`. -/
theorem norm_riemannZeta_sub_sum_sawtooth_le {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    {a : ℝ} (ha : 0 < a) :
    ‖riemannZeta s -
        ((∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) +
          (a : ℂ) ^ (1 - s) / (s - 1) +
          (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s))‖ ≤
      ‖s‖ * a ^ (-s.re) / (2 * s.re) := by
  have hsub :
      riemannZeta s -
          ((∑ n ∈ Finset.Icc 1 ⌊a⌋₊, (n : ℂ) ^ (-s)) +
            (a : ℂ) ^ (1 - s) / (s - 1) +
            (bernoulliFun 1 (Int.fract a) : ℂ) * (a : ℂ) ^ (-s)) =
        -(s * ∫ t in Set.Ioi a, (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [riemannZeta_eq_sum_add_integral_sawtooth hs hs₁ ha]
    ring
  rw [hsub, norm_neg, norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_integral_Ioi_bernoulliFun_one_fract_mul_cpow_le ha hs)
    (norm_nonneg s)

/-- **Integer-cutoff Euler–Maclaurin truncation bound.** On `0 < re s`, `s ≠ 1`, for any integer
`1 ≤ N`, the trapezoidal Euler–Maclaurin approximation to `riemannZeta s` has error norm at most
`‖s‖ * N ^ (-re s) / (2 * re s)`. -/
theorem norm_riemannZeta_sub_sum_nat_sawtooth_le {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s -
        ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) +
          (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2)‖ ≤
      ‖s‖ * (N : ℝ) ^ (-s.re) / (2 * s.re) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsub :
      riemannZeta s -
          ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) +
            (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2) =
        -(s * ∫ t in Set.Ioi (N : ℝ),
          (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [riemannZeta_eq_sum_nat_add_integral_sawtooth hs hs₁ hN]
    ring
  rw [hsub, norm_neg, norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_integral_Ioi_bernoulliFun_one_fract_mul_cpow_le hN0 hs)
    (norm_nonneg s)

/-- **Half-integer-cutoff Euler–Maclaurin truncation bound.** On `0 < re s`, `s ≠ 1`, for any
`N : ℕ` (including `N = 0`), the midpoint approximation at `N + 1 / 2` has no boundary term and
error norm at most `‖s‖ * (N + 1 / 2) ^ (-re s) / (2 * re s)`. -/
theorem norm_riemannZeta_sub_sum_half_sawtooth_le {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) (N : ℕ) :
    ‖riemannZeta s -
        ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) +
          ((N : ℂ) + 1 / 2) ^ (1 - s) / (s - 1))‖ ≤
      ‖s‖ * ((N : ℝ) + 1 / 2) ^ (-s.re) / (2 * s.re) := by
  have ha : 0 < (N : ℝ) + 1 / 2 := by positivity
  have hsub :
      riemannZeta s -
          ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) +
            ((N : ℂ) + 1 / 2) ^ (1 - s) / (s - 1)) =
        -(s * ∫ t in Set.Ioi ((N : ℝ) + 1 / 2),
          (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [riemannZeta_eq_sum_half_add_integral_sawtooth hs hs₁ N]
    ring
  rw [hsub, norm_neg, norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_integral_Ioi_bernoulliFun_one_fract_mul_cpow_le ha hs)
    (norm_nonneg s)

/-- Throughout `0 < re s` (including `s = 1`), the pole-removed zeta function `riemannZeta₀ s`
differs from `1 / 2` by at most `‖s‖ / (2 * re s)` in norm. -/
theorem norm_riemannZeta₀_sub_one_half_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s - 1 / 2‖ ≤ ‖s‖ / (2 * s.re) := by
  have hsub : riemannZeta₀ s - 1 / 2 =
      -(s * ∫ t in Set.Ioi (1 : ℝ),
        (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [riemannZeta₀_eq_one_half_sub_integral_sawtooth hs]
    ring
  rw [hsub, norm_neg, norm_mul]
  have hI := norm_integral_Ioi_bernoulliFun_one_fract_mul_cpow_le zero_lt_one hs
  rw [Real.one_rpow] at hI
  calc
    ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ),
        (bernoulliFun 1 (Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
        ‖s‖ * (1 / (2 * s.re)) := mul_le_mul_of_nonneg_left hI (norm_nonneg s)
    _ = ‖s‖ / (2 * s.re) := by ring

/-- Throughout `0 < re s` (including `s = 1`), `‖riemannZeta₀ s - 1‖ ≤ ‖s‖ / re s`. -/
theorem norm_riemannZeta₀_sub_one_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s - 1‖ ≤ ‖s‖ / s.re := by
  have hsub : riemannZeta₀ s - 1 =
      -(s * ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [riemannZeta₀_eq_one_sub_integral_fract hs]
    ring
  rw [hsub, norm_neg, norm_mul]
  have hI := norm_integral_Ioi_fract_mul_cpow_le zero_lt_one hs
  rw [Real.one_rpow] at hI
  calc
    ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
        ‖s‖ * (1 / s.re) := mul_le_mul_of_nonneg_left hI (norm_nonneg s)
    _ = ‖s‖ / s.re := by ring

/-! ### Explicit linear upper bounds in the right half-plane and on Borel–Carathéodory discs -/

/-- **Right-half-plane norm bound for `riemannZeta`.** For every `z` with `0 < re z` and `z ≠ 1`,
`‖ζ(z)‖ ≤ 1 / 2 + 1 / ‖z - 1‖ + ‖z‖ / (2 * re z)`. -/
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

/-- Away from the real axis (`1 ≤ |im z|`) in the half-plane `1 / 2 ≤ re z`, the polar term is at
most `1` and `2 * re z ≥ 1`, giving the clean linear bound `‖ζ(z)‖ ≤ 3 / 2 + ‖z‖`. -/
theorem norm_riemannZeta_le_three_halves_add_norm {z : ℂ} (hre : 1 / 2 ≤ z.re)
    (him : 1 ≤ |z.im|) :
    ‖riemannZeta z‖ ≤ 3 / 2 + ‖z‖ := by
  have hz0 : 0 < z.re := by linarith
  have hz₁ : z ≠ 1 := fun h ↦ by
    rw [h, one_im, abs_zero] at him
    linarith
  have hpole : 1 ≤ ‖z - 1‖ := by
    calc
      (1 : ℝ) ≤ |z.im| := him
      _ = |(z - 1).im| := by simp
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm (z - 1)
  have hinv : 1 / ‖z - 1‖ ≤ 1 := div_le_one_of_le₀ hpole (norm_nonneg _)
  have hdiv : ‖z‖ / (2 * z.re) ≤ ‖z‖ :=
    div_le_self (norm_nonneg z) (by linarith)
  linarith [norm_riemannZeta_le_one_half_add_inv_add_div hz0 hz₁]

/-- **Explicit linear growth on unit discs centered at `3 / 2 + t * I`.** For `2 ≤ |t|` and
`‖w‖ ≤ 1`, the point `w + 3 / 2 + t * I` lies in `re z ≥ 1 / 2`, `|im z| ≥ 1`, and satisfies
`‖ζ(w + 3 / 2 + t * I)‖ ≤ 4 + |t|`. -/
theorem norm_riemannZeta_le_linear {t : ℝ} (ht : 2 ≤ |t|) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖riemannZeta (w + 3 / 2 + t * I)‖ ≤ 4 + |t| := by
  set z : ℂ := w + 3 / 2 + t * I
  have hw_re : |w.re| ≤ 1 := (Complex.abs_re_le_norm w).trans hw
  have hw_im : |w.im| ≤ 1 := (Complex.abs_im_le_norm w).trans hw
  have hz_re : 1 / 2 ≤ z.re := by
    have hre_eq : z.re = w.re + 3 / 2 := by simp [z]
    linarith [(abs_le.mp hw_re).1]
  have hz_im : 1 ≤ |z.im| := by
    have him_eq : z.im = w.im + t := by simp [z]
    have htri : |t| - |w.im| ≤ |w.im + t| := by
      have h := abs_sub_abs_le_abs_sub t (-w.im)
      simpa only [abs_neg, sub_neg_eq_add, add_comm t] using h
    rw [him_eq]
    linarith
  have hnorm : ‖z‖ ≤ 5 / 2 + |t| := by
    have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    have htI : ‖(t : ℂ) * I‖ = |t| := by simp [Complex.norm_real]
    have htri1 := norm_add_le (w + 3 / 2) ((t : ℂ) * I)
    have htri2 := norm_add_le w (3 / 2 : ℂ)
    linarith
  linarith [norm_riemannZeta_le_three_halves_add_norm hz_re hz_im]

/-- Closed-ball form of `TauCeti.norm_riemannZeta_le_linear`: for `2 ≤ |t|` and
`z ∈ Metric.closedBall (3 / 2 + t * I) 1`, `‖ζ(z)‖ ≤ 4 + |t|`. -/
theorem norm_riemannZeta_le_of_mem_closedBall {t : ℝ} (ht : 2 ≤ |t|) {z : ℂ}
    (hz : z ∈ Metric.closedBall (3 / 2 + t * I) 1) :
    ‖riemannZeta z‖ ≤ 4 + |t| := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hdecomp : z = (z - (3 / 2 + t * I)) + 3 / 2 + t * I := by ring
  rw [hdecomp]
  exact norm_riemannZeta_le_linear ht hz

/-! ### Real-axis `(1, ∞)` comparison, strict antitonicity, and `1 < re s` majorants -/

/-- For every real `σ > 1`, the real part of `riemannZeta σ` is strictly greater than `1` (the
`n = 1` term of the `p`-series contributes `1` and the `n = 2` term contributes `2 ^ (-σ) > 0`). -/
theorem one_lt_riemannZeta_re {σ : ℝ} (hσ : 1 < σ) : 1 < (riemannZeta σ).re := by
  have hsum := hasSum_nat_add_one_rpow_neg_riemannZeta_re hσ
  have hpair := sum_le_hasSum ({0, 1} : Finset ℕ)
    (fun n _ ↦ by positivity) hsum
  rw [Finset.sum_pair zero_ne_one] at hpair
  simp only [Nat.cast_zero, zero_add, Real.one_rpow, Nat.cast_one] at hpair
  have h2 : (0 : ℝ) < (1 + 1) ^ (-σ) := by positivity
  linarith

/-- On `(1, ∞)`, the real function `σ ↦ Re ζ(σ)` is strictly decreasing. -/
theorem strictAntiOn_riemannZeta_re :
    StrictAntiOn (fun σ : ℝ ↦ (riemannZeta σ).re) (Set.Ioi 1) := by
  have hanti := TauCeti.LSeries.strictAntiOn_re_of_exists_pos (a := 1)
    (fun _ ↦ zero_le_one) ⟨2, le_rfl, zero_lt_one⟩
  intro x hx y hy hxy
  have hxS : LSeriesSummable 1 (x : ℂ) := LSeriesSummable_one_iff.mpr (by simpa using hx)
  have hyS : LSeriesSummable 1 (y : ℂ) := LSeriesSummable_one_iff.mpr (by simpa using hy)
  dsimp only
  rw [← LSeries_one_eq_riemannZeta (by simpa using hy),
    ← LSeries_one_eq_riemannZeta (by simpa using hx)]
  exact hanti hxS hyS hxy

private lemma riemannZeta_ofReal_re_eq_div_sub_integral_fract {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re =
      σ / (σ - 1) - σ * ∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(σ + 1)) := by
  have hσ0 : 0 < ((σ : ℂ)).re := by simpa using zero_lt_one.trans hσ
  have hσ1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
  have hrep := riemannZeta_eq_div_sub_integral_fract hσ0 hσ1
  have hI : (∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-((σ : ℂ) + 1))) =
      ((∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(σ + 1)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
    rw [ofReal_mul, ofReal_cpow ht0, ofReal_neg, ofReal_add, ofReal_one]
  have hdiv : (σ : ℂ) / ((σ : ℂ) - 1) = ((σ / (σ - 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hI, hdiv, ← ofReal_mul, ← ofReal_sub] at hrep
  simpa only [ofReal_re] using congrArg Complex.re hrep

private lemma integrableOn_Ioi_real_fract_mul_rpow {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ ↦ Int.fract t * t ^ (-(σ + 1))) (Set.Ioi 1) := by
  have hc := integrableOn_Ioi_fract_mul_cpow zero_lt_one (s := (σ : ℂ)) (by simpa using hσ)
  have heq : Set.EqOn (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-((σ : ℂ) + 1)))
      (fun t : ℝ ↦ ((Int.fract t * t ^ (-(σ + 1)) : ℝ) : ℂ)) (Set.Ioi 1) := fun t ht ↦ by
    have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
    dsimp only
    rw [ofReal_mul, ofReal_cpow ht0, ofReal_neg, ofReal_add, ofReal_one]
  simpa using (hc.congr_fun heq measurableSet_Ioi).re

private lemma setIntegral_Ioi_pos_of_pos_on_Ioo {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Ioi 1)) (hnonneg : ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ g t)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) (hpos : ∀ t ∈ Set.Ioo a b, 0 < g t) :
    0 < ∫ t in Set.Ioi (1 : ℝ), g t := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi 1 := fun t ht ↦ ha.trans_lt ht.1
  have hstep : 0 < ∫ t in a..b, g t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr (hg.mono_set hsub)) hpos hab
  rw [intervalIntegral.integral_of_le hab.le] at hstep
  exact hstep.trans_le <| setIntegral_mono_set hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hnonneg) hsub.eventuallySubset

/-- **Strict Laurent lower bound on `(1, ∞)`.** For every real `σ > 1`,
`1 / (σ - 1) < Re ζ(σ)`. -/
theorem one_div_sub_one_lt_riemannZeta_re {σ : ℝ} (hσ : 1 < σ) :
    1 / (σ - 1) < (riemannZeta σ).re := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hint_f : IntegrableOn (fun t : ℝ ↦ Int.fract t * t ^ (-(σ + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_real_fract_mul_rpow hσ0
  have hint_r : IntegrableOn (fun t : ℝ ↦ t ^ (-(σ + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hint_sub : IntegrableOn (fun t : ℝ ↦ (1 - Int.fract t) * t ^ (-(σ + 1))) (Set.Ioi 1) := by
    refine (hint_r.sub hint_f).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only [Pi.sub_apply]
    ring
  have hpos_sub : 0 < ∫ t in Set.Ioi (1 : ℝ), (1 - Int.fract t) * t ^ (-(σ + 1)) :=
    setIntegral_Ioi_pos_of_pos_on_Ioo hint_sub
      (fun t ht ↦ mul_nonneg (sub_nonneg.mpr (Int.fract_lt_one t).le)
        (Real.rpow_nonneg (zero_lt_one.trans ht).le _))
      le_rfl (a := 1) (b := 3 / 2) (by norm_num) fun t ht ↦
        mul_pos (sub_pos.mpr (Int.fract_lt_one t)) (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
  have hI_sum : (∫ t in Set.Ioi (1 : ℝ), (1 - Int.fract t) * t ^ (-(σ + 1))) +
      (∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(σ + 1))) = 1 / σ := by
    rw [← integral_add hint_sub hint_f]
    have hcongr : (∫ t in Set.Ioi (1 : ℝ),
        (1 - Int.fract t) * t ^ (-(σ + 1)) + Int.fract t * t ^ (-(σ + 1))) =
        ∫ t in Set.Ioi (1 : ℝ), t ^ (-(σ + 1)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by ring
    rw [hcongr, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    ring
  have hmul : σ * (∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(σ + 1))) < 1 := by
    have hmul_eq : σ * ((∫ t in Set.Ioi (1 : ℝ), (1 - Int.fract t) * t ^ (-(σ + 1))) +
        ∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(σ + 1))) = 1 := by
      rw [hI_sum, mul_one_div_cancel hσ0.ne']
    nlinarith [mul_pos hσ0 hpos_sub]
  have halg : σ / (σ - 1) = 1 / (σ - 1) + 1 := by
    have hne : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
    field_simp [hne]
    ring
  rw [riemannZeta_ofReal_re_eq_div_sub_integral_fract hσ, halg]
  linarith

/-- **Strict Laurent upper bound on `(1, ∞)`.** For every real `σ > 1`,
`Re ζ(σ) < 1 + 1 / (σ - 1)`. -/
theorem riemannZeta_re_lt_one_add_one_div_sub_one {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re < 1 + 1 / (σ - 1) := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hint_f : IntegrableOn (fun t : ℝ ↦ Int.fract t * t ^ (-(σ + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_real_fract_mul_rpow hσ0
  have hpos_f : 0 < ∫ t in Set.Ioi (1 : ℝ), Int.fract t * t ^ (-(σ + 1)) :=
    setIntegral_Ioi_pos_of_pos_on_Ioo hint_f
      (fun t ht ↦ mul_nonneg (Int.fract_nonneg t) (Real.rpow_nonneg (zero_lt_one.trans ht).le _))
      (a := 5 / 4) (b := 7 / 4) (by norm_num) (by norm_num) fun t ht ↦ by
        have hfl : ⌊t⌋ = 1 := Int.floor_eq_iff.mpr ⟨by norm_num; linarith [ht.1],
          by norm_num; linarith [ht.2]⟩
        have hfr : 0 < Int.fract t := by
          rw [Int.fract, hfl]
          norm_num
          linarith [ht.1]
        exact mul_pos hfr (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
  have halg : σ / (σ - 1) = 1 + 1 / (σ - 1) := by
    have hne : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
    field_simp [hne]
    ring
  rw [riemannZeta_ofReal_re_eq_div_sub_integral_fract hσ, halg]
  linarith [mul_pos hσ0 hpos_f]

/-- **Dirichlet-series triangle-inequality majorant on `1 < re s`.** At any complex point `s` in
the half-plane of absolute convergence `1 < re s`, `‖ζ(s)‖ ≤ Re ζ(re s)`. -/
theorem norm_riemannZeta_le_riemannZeta_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ (riemannZeta s.re).re := by
  rw [← LSeries_one_eq_riemannZeta hs, ← LSeries_one_eq_riemannZeta (by simpa using hs)]
  exact TauCeti.LSeries.norm_LSeries_le_re_of_nonneg (fun _ ↦ zero_le_one) s

/-- On the entire half-plane `1 < re s`, `‖ζ(s)‖ < 1 + 1 / (re s - 1)`. -/
theorem norm_riemannZeta_lt_one_add_one_div_sub_one {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ < 1 + 1 / (s.re - 1) :=
  (norm_riemannZeta_le_riemannZeta_re hs).trans_lt (riemannZeta_re_lt_one_add_one_div_sub_one hs)

end TauCeti
