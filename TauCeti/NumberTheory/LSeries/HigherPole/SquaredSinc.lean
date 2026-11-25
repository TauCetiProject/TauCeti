/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Integrals.SincSq
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Fejer

/-!
# The normalised squared-sinc kernel

For real `λ` and `v` this file defines the kernel

`K_λ(v) = squaredSinc λ v = (λ / π) * sinc (λ v) ^ 2`,

with Mathlib's `Real.sinc` (so `sinc 0 = 1`). For `λ > 0` it is a continuous probability density
on `ℝ`, and it is the inverse Fourier transform, in angular frequency, of the triangle
`1 - |y| / (2λ)` supported on `[-2λ, 2λ]`:

`K_λ(v) = (1 / 2π) ∫_{-2λ}^{2λ} (1 - |y| / (2λ)) e^{i y v} dy`.

As `λ → ∞` its mass concentrates at the origin. These are the properties a Tauberian argument
needs from a smoothing kernel: positivity and concentration let monotonicity remove the smoothing,
while the triangle formula, an integral over the compact frequency range `[-2λ, 2λ]`, means that
the smoothed function is controlled by boundary values of a Laplace transform on a compact segment
only.

## Main definitions

* `TauCeti.HigherPoleTauberian.squaredSinc`: the kernel `K_λ(v)`, total in `λ` and `v`.

## Main results

* `squaredSinc_nonneg`, `squaredSinc_le`, `squaredSinc_neg_right`, `continuous_squaredSinc`,
  `integrable_squaredSinc`: positivity, the bound `K_λ ≤ λ / π`, evenness, continuity and
  integrability.
* `squaredSinc_intCast_mul_pi_div`, `squaredSinc_pi_div`: `K_λ` vanishes at the nonzero multiples
  of `π / λ`.
* `squaredSinc_mass`: `∫ v, K_λ v = 1` for `λ > 0`.
* `squaredSinc_fourier`: the triangle formula above, for `λ ≥ 0` and every `v`.
* `tendsto_intervalIntegral_squaredSinc`, `tendsto_integral_squaredSinc_tail`: for `h > 0`, the
  mass of `[-h, h]` tends to `1` and the mass of `{v | h ≤ |v|}` tends to `0` as `λ → ∞`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242: §3.3.3–3.3.5, pp. 224–226 (a continuous weight on `[-2λ, 2λ]`, its Fourier
  transform, and the choice of the triangle), and §3.4, pp. 227–228 (positivity of the kernel, its
  mass near the origin and its tails). Delange's kernel is the unnormalised transform of the same
  triangle, `π K_λ`.
-/

public section

noncomputable section

open MeasureTheory Filter Set Real
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-- **The normalised squared-sinc kernel** `K_λ(v) = (λ / π) * sinc (λ v) ^ 2`, written
`squaredSinc ell v` with `ell = λ`.

The definition is total. For `λ > 0` it is a probability density on `ℝ` (`squaredSinc_mass`), and
for `λ ≥ 0` it is the inverse Fourier transform, in angular frequency, of the triangle
`1 - |y| / (2λ)` on `[-2λ, 2λ]` (`squaredSinc_fourier`). -/
def squaredSinc (ell v : ℝ) : ℝ :=
  ell / π * sinc (ell * v) ^ 2

variable {ell h : ℝ}

/-- The defining formula of `squaredSinc`. -/
theorem squaredSinc_def (ell v : ℝ) : squaredSinc ell v = ell / π * sinc (ell * v) ^ 2 := (rfl)

/-- The value at the origin is `λ / π`. -/
@[simp]
theorem squaredSinc_zero_right (ell : ℝ) : squaredSinc ell 0 = ell / π := by
  simp [squaredSinc_def]

/-- The kernel of bandwidth `0` vanishes. -/
@[simp]
theorem squaredSinc_zero_left (v : ℝ) : squaredSinc 0 v = 0 := by
  simp [squaredSinc_def]

/-- The kernel is even. -/
@[simp]
theorem squaredSinc_neg_right (ell v : ℝ) : squaredSinc ell (-v) = squaredSinc ell v := by
  simp [squaredSinc_def]

/-- The kernel is nonnegative for a nonnegative bandwidth. -/
theorem squaredSinc_nonneg (hell : 0 ≤ ell) (v : ℝ) : 0 ≤ squaredSinc ell v := by
  rw [squaredSinc_def]
  positivity

/-- The kernel is bounded by its value `λ / π` at the origin. -/
theorem squaredSinc_le (hell : 0 ≤ ell) (v : ℝ) : squaredSinc ell v ≤ ell / π := by
  rw [squaredSinc_def]
  exact mul_le_of_le_one_right (by positivity)
    ((sq_le_one_iff_abs_le_one _).2 (abs_sinc_le_one _))

/-- The kernel vanishes at every nonzero integer multiple of `π / λ`. -/
theorem squaredSinc_intCast_mul_pi_div (ell : ℝ) {n : ℤ} (hn : n ≠ 0) :
    squaredSinc ell (n * π / ell) = 0 := by
  rcases eq_or_ne ell 0 with rfl | hell
  · simp
  have harg : ell * (n * π / ell) = n * π := by field_simp
  have hne : (n : ℝ) * π ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hn) pi_ne_zero
  simp [squaredSinc_def, harg, sinc_of_ne_zero hne, sin_int_mul_pi]

/-- The kernel vanishes at `π / λ`. -/
@[simp]
theorem squaredSinc_pi_div (ell : ℝ) : squaredSinc ell (π / ell) = 0 := by
  simpa using squaredSinc_intCast_mul_pi_div ell one_ne_zero

/-- The kernel is continuous for every bandwidth. -/
@[fun_prop]
theorem continuous_squaredSinc (ell : ℝ) : Continuous (squaredSinc ell) := by
  rw [funext (squaredSinc_def ell)]
  fun_prop

/-- The kernel is Lebesgue integrable on `ℝ` for every bandwidth. -/
theorem integrable_squaredSinc (ell : ℝ) : Integrable (squaredSinc ell) := by
  rcases eq_or_ne ell 0 with rfl | hell
  · simp_rw [funext squaredSinc_zero_left]
    exact integrable_zero _ _ _
  rw [funext (squaredSinc_def ell)]
  exact (integrable_sinc_sq.comp_mul_left' hell).const_mul _

/-- **The kernel has total mass one.** -/
theorem squaredSinc_mass (hell : 0 < ell) : ∫ v, squaredSinc ell v = 1 := by
  simp_rw [squaredSinc_def]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun w ↦ sinc w ^ 2) ell,
    integral_sinc_sq, smul_eq_mul, abs_of_pos (inv_pos.2 hell)]
  field_simp

/-! ### Concentration at the origin -/

/-- The mass of `[-h, h]` is `(1 / π) ∫_{-λh}^{λh} sinc²`. -/
private theorem intervalIntegral_squaredSinc (hell : 0 < ell) (h : ℝ) :
    ∫ v in -h..h, squaredSinc ell v = π⁻¹ * ∫ w in -(ell * h)..ell * h, sinc w ^ 2 := by
  simp_rw [squaredSinc_def]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun w ↦ sinc w ^ 2) hell.ne', smul_eq_mul, mul_neg]
  field_simp

/-- **Concentration**: for `h > 0`, the mass of `K_λ` on `[-h, h]` tends to `1` as `λ → ∞`. -/
theorem tendsto_intervalIntegral_squaredSinc (hh : 0 < h) :
    Tendsto (fun ell ↦ ∫ v in -h..h, squaredSinc ell v) atTop (𝓝 1) := by
  have hb : Tendsto (fun ell : ℝ ↦ ell * h) atTop atTop := tendsto_id.atTop_mul_const hh
  have hlim := (intervalIntegral_tendsto_integral integrable_sinc_sq
    (tendsto_neg_atTop_atBot.comp hb) hb).const_mul π⁻¹
  rw [integral_sinc_sq, inv_mul_cancel₀ pi_ne_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ell hell
  exact (intervalIntegral_squaredSinc hell h).symm

/-- **Tail concentration**: for `h > 0`, the mass of `K_λ` on `{v | h ≤ |v|}` tends to `0` as
`λ → ∞`. -/
theorem tendsto_integral_squaredSinc_tail (hh : 0 < h) :
    Tendsto (fun ell ↦ ∫ v in {v | h ≤ |v|}, squaredSinc ell v) atTop (𝓝 0) := by
  have hs : MeasurableSet {v : ℝ | h ≤ |v|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hcompl : {v : ℝ | h ≤ |v|}ᶜ = Ioo (-h) h := by
    ext v
    simp [abs_lt]
  have hlim := (tendsto_intervalIntegral_squaredSinc hh).const_sub 1
  rw [sub_self] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ell hell
  rw [← squaredSinc_mass hell, ← integral_add_compl hs (integrable_squaredSinc ell), hcompl,
    intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
    add_sub_cancel_right]

/-! ### The triangle formula -/

/-- **The kernel is the inverse Fourier transform of the triangle.** For `λ ≥ 0` and every `v`,
`K_λ(v) = (1 / 2π) ∫_{-2λ}^{2λ} (1 - |y| / (2λ)) e^{i y v} dy`, the inverse Fourier transform, in
angular frequency, of the triangle `1 - |y| / (2λ)` supported on `[-2λ, 2λ]`. -/
theorem squaredSinc_fourier (hell : 0 ≤ ell) (v : ℝ) :
    (squaredSinc ell v : ℂ) = 1 / (2 * π) *
      ∫ y : ℝ in (-(2 * ell))..(2 * ell),
        ((1 - |y| / (2 * ell) : ℝ) : ℂ) * Complex.exp (Complex.I * y * v) := by
  set L := 2 * ell with hLdef
  have hL : 0 ≤ L := by positivity
  set f : ℝ → ℂ := fun y ↦ ((1 - |y| / L : ℝ) : ℂ) * Complex.exp (Complex.I * y * v) with hf
  have hfc : Continuous f := by fun_prop
  -- Fold the integral over `[-L, 0]` onto `[0, L]` by `y ↦ -y`.
  have hsplit : ∫ y in (-L)..L, f y = ∫ y in 0..L, (f (-y) + f y) := by
    have hneg : IntervalIntegrable (fun y ↦ f (-y)) volume 0 L :=
      (hfc.comp continuous_neg).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hneg (hfc.intervalIntegrable _ _),
      intervalIntegral.integral_comp_neg f, neg_zero]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)).symm
  -- On `[0, L]` the even part is the real function `2 (1 - y / L) cos (y v)`.
  have heven : ∫ y in 0..L, (f (-y) + f y) =
      ((2 * ∫ y in 0..L, (1 - y / L) * cos (y * v) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    rw [uIcc_of_le hL] at hy
    have hcos : Complex.exp (Complex.I * (-y : ℝ) * v) + Complex.exp (Complex.I * y * v) =
        2 * (cos (y * v) : ℂ) := by
      rw [Complex.ofReal_cos, Complex.two_cos]
      push_cast
      ring_nf
    simp only [hf, abs_neg, abs_of_nonneg hy.1, ← mul_add, hcos]
    push_cast
    ring
  rw [hsplit, heven, integral_one_sub_div_mul_cos_mul, squaredSinc_def, hLdef]
  have harg : 2 * ell * v / 2 = ell * v := by ring
  rw [harg]
  push_cast
  ring

end TauCeti.HigherPoleTauberian
