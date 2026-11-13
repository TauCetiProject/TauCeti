/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.Uniqueness

/-!
# Completeness of the Fourier sine system on an interval

On an interval `[a, b]` with `a < b`, the functions `x ↦ sin (k π (x - a) / (b - a))`,
`k = 1, 2, …`, are the eigenfunctions of `-d²/dx²` with zero boundary values at both ends. This
file proves that they form a **complete** system: an integrable function on `(a, b]` orthogonal to
all of them vanishes almost everywhere (`TauCeti.ae_eq_zero_of_forall_integral_mul_sin_eq_zero`).
This covers in particular every function in `L²(a, b)`. The theorem does not assume `a < b`: when
`b ≤ a` the interval `(a, b]` is empty, so the restricted measure is zero and the conclusion holds
trivially.

For `a < b`, the proof reduces to the uniqueness of Fourier coefficients of integrable functions
on an interval (`MeasureTheory.IntegrableOn.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero`). Extend
`g` oddly about `a` to `[2a - b, b]`. On this interval of length `2(b - a)`, the `n`-th Fourier
coefficient of the odd extension is a multiple of `∫ g(x) sin (n π (x - a) / (b - a)) dx`, so all
of them vanish, and uniqueness forces the extension, hence `g`, to vanish almost everywhere.

## Main results

* `TauCeti.ae_eq_zero_of_forall_integral_mul_sin_eq_zero`: completeness of the sine system
  `sin (k π (x - a) / (b - a))`, `k ≥ 1`, among the integrable functions on `(a, b]`.

## References

* G. B. Folland, *Fourier Analysis and its Applications*, Section 2.4 (odd extensions and
  Fourier sine series) and Section 3.4 (completeness of the trigonometric system).
-/

public section

open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval

namespace TauCeti

variable {a b : ℝ}

/-- The difference of a Fourier monomial on `[2a - b, b]` at `y` and at its reflection `2a - y`
about `a` is a multiple of `sin (n π (y - a) / (b - a))`. -/
private theorem fourier_sub_fourier_reflect (hab : a < b) (n : ℤ) (y : ℝ) :
    fourier (-n) (y : AddCircle (b - (2 * a - b))) -
        fourier (-n) ((2 * a - y : ℝ) : AddCircle (b - (2 * a - b))) =
      -2 * I * exp (-(π * I * n * a / (b - a))) * (Real.sin (n * π * (y - a) / (b - a)) : ℂ) := by
  have hba : (b : ℂ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab.ne')
  set C : ℂ := -(π * I * n * a / (b - a))
  set Y : ℂ := ((n * π * (y - a) / (b - a) : ℝ) : ℂ)
  have hrhs : -2 * I * exp C * ((exp (-Y * I) - exp (Y * I)) * I / 2) =
      exp (C + -Y * I) - exp (C + Y * I) := by
    rw [exp_add, exp_add]
    linear_combination (-(exp C * exp (-Y * I) - exp C * exp (Y * I))) * I_sq
  rw [fourier_coe_apply, fourier_coe_apply, ofReal_sin, sin, hrhs]
  congr 2 <;>
  · simp only [C, Y]
    push_cast
    rw [show (b : ℂ) - (2 * a - b) = 2 * (b - a) by ring]
    field_simp
    ring

/-- Orthogonality to the sines `sin (k π (x - a) / (b - a))` for `k ≥ 1` extends to every integer
frequency, since `sin` is odd. -/
private theorem integral_mul_sin_intCast_eq_zero {g : ℝ → ℝ}
    (h : ∀ k : ℕ, 0 < k → ∫ x in a..b, g x * Real.sin (k * π * (x - a) / (b - a)) = 0)
    (n : ℤ) : ∫ x in a..b, g x * Real.sin (n * π * (x - a) / (b - a)) = 0 := by
  rcases n with k | k
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simpa using h k hk
  · have hk := h (k + 1) k.succ_pos
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_mul, neg_div, Real.sin_neg,
      mul_neg, intervalIntegral.integral_neg, neg_eq_zero]
    simpa using hk

/-- The odd extension of `g` about `a`: equal to `g` to the right of `a` and to
`x ↦ -g (2a - x)` at and to the left of `a`. -/
private noncomputable def oddExtension (a : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℂ :=
  if a < x then (g x : ℂ) else -(g (2 * a - x) : ℂ)

private theorem oddExtension_of_lt {g : ℝ → ℝ} {x : ℝ} (hx : a < x) :
    oddExtension a g x = g x := by
  simp [oddExtension, hx]

private theorem oddExtension_of_le {g : ℝ → ℝ} {x : ℝ} (hx : x ≤ a) :
    oddExtension a g x = -(g (2 * a - x) : ℂ) := by
  simp [oddExtension, hx.not_gt]

/-- The odd extension of a function integrable on `[a, b]` is integrable on the reflected
interval `[2a - b, a]`. -/
private theorem intervalIntegrable_oddExtension_left (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => (g x : ℂ)) volume a b) :
    IntervalIntegrable (oddExtension a g) volume (2 * a - b) a := by
  have hg' : IntervalIntegrable (fun x => (g (2 * a - x) : ℂ)) volume (2 * a - b) a := by
    simpa [show 2 * a - a = a by ring] using (hg.comp_sub_left (2 * a)).symm
  refine hg'.neg.congr_ae ?_
  rw [uIoc_of_le (by linarith)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Pi.neg_apply, oddExtension_of_le hx.2]

/-- The odd extension of a function integrable on `[a, b]` is integrable on `[a, b]`. -/
private theorem intervalIntegrable_oddExtension_right (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => (g x : ℂ)) volume a b) :
    IntervalIntegrable (oddExtension a g) volume a b := by
  refine hg.congr_ae ?_
  rw [uIoc_of_le hab]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [oddExtension_of_lt hx.1]

/-- Integrating a continuous `F` against the odd extension of `g` over `[2a - b, b]` folds the
left half onto `[a, b]` by the substitution `x = 2a - y`. -/
private theorem integral_mul_oddExtension (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => (g x : ℂ)) volume a b) {F : ℝ → ℂ} (hFc : Continuous F) :
    ∫ x in (2 * a - b)..b, F x * oddExtension a g x =
      ∫ y in a..b, (F y - F (2 * a - y)) * (g y : ℂ) := by
  -- On `[2a - b, a]` substitute `x = 2a - y`; on `(a, b]` the extension is `g` itself.
  have hleft : ∫ x in (2 * a - b)..a, F x * oddExtension a g x =
      ∫ y in a..b, F (2 * a - y) * -(g y : ℂ) := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun x => F x * -(g (2 * a - x) : ℂ)) (a := a) (b := b) (2 * a)
    simp only [sub_sub_cancel, show 2 * a - a = a by ring] at hsub
    rw [hsub]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rw [oddExtension_of_le hx.2]
  have hright : ∫ x in a..b, F x * oddExtension a g x = ∫ y in a..b, F y * (g y : ℂ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hab] at hx
    rw [oddExtension_of_lt hx.1]
  have hint1 : IntervalIntegrable (fun y => F y * (g y : ℂ)) volume a b :=
    hg.continuousOn_mul hFc.continuousOn
  have hint2 : IntervalIntegrable (fun y => F (2 * a - y) * -(g y : ℂ)) volume a b :=
    hg.neg.continuousOn_mul (hFc.comp (continuous_const.sub continuous_id)).continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_oddExtension_left hab hg).continuousOn_mul hFc.continuousOn)
      ((intervalIntegrable_oddExtension_right hab hg).continuousOn_mul hFc.continuousOn),
    hleft, hright, ← intervalIntegral.integral_add hint2 hint1]
  congr 1 with y
  ring

/-- The Fourier coefficients on `[2a - b, b]` of the odd extension of `g` about `a` are multiples
of the integrals of `g` against `sin (n π (x - a) / (b - a))` over `[a, b]`; under orthogonality
to all of these they vanish. -/
private theorem fourierCoeffOn_oddExtension_eq_zero (hab : a < b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable (fun x => (g x : ℂ)) volume a b)
    (hZ : ∀ n : ℤ, ∫ x in a..b, g x * Real.sin (n * π * (x - a) / (b - a)) = 0) (n : ℤ) :
    fourierCoeffOn (by linarith : 2 * a - b < b) (oddExtension a g) n = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp only [smul_eq_mul]
  rw [integral_mul_oddExtension hab.le hg
    (F := fun x : ℝ => fourier (-n) (x : AddCircle (b - (2 * a - b))))
    ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _))]
  have hpt : ∀ y : ℝ, (fourier (-n) (y : AddCircle (b - (2 * a - b))) -
      fourier (-n) ((2 * a - y : ℝ) : AddCircle (b - (2 * a - b)))) * (g y : ℂ) =
        -2 * I * exp (-(π * I * n * a / (b - a))) *
          ((g y * Real.sin (n * π * (y - a) / (b - a)) : ℝ) : ℂ) := fun y => by
    rw [fourier_sub_fourier_reflect hab n y, ofReal_mul]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hZ n]
  simp

/-- **Completeness of the Fourier sine system.** A function `g` integrable on `(a, b]` with

`∫ x in a..b, g x * sin (k π (x - a) / (b - a)) = 0` for every `k ≥ 1`

vanishes almost everywhere on `(a, b]`. For `a < b` these sines are the Dirichlet eigenfunctions
of `-d²/dx²` on `(a, b)`, so this is the completeness half of the Fourier sine expansion. For
`b ≤ a` the interval `(a, b]` is empty, the restricted measure is zero, and the conclusion holds
trivially. -/
theorem ae_eq_zero_of_forall_integral_mul_sin_eq_zero {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc a b))
    (h : ∀ k : ℕ, 0 < k → ∫ x in a..b, g x * Real.sin (k * π * (x - a) / (b - a)) = 0) :
    g =ᵐ[volume.restrict (Ioc a b)] 0 := by
  by_cases hab : a < b
  · have hgi : IntervalIntegrable (fun x => (g x : ℂ)) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hg.ofReal
    have hzero := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_left (by linarith : 2 * a - b ≤ a))
      (IntegrableOn.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero _
        ((intervalIntegrable_oddExtension_left hab.le hgi).trans
          (intervalIntegrable_oddExtension_right hab.le hgi)).1
        (fourierCoeffOn_oddExtension_eq_zero hab hgi (integral_mul_sin_intCast_eq_zero h)))
    filter_upwards [hzero, ae_restrict_mem measurableSet_Ioc] with x hx hxm
    rw [Pi.zero_apply, oddExtension_of_lt hxm.1] at hx
    exact_mod_cast hx
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hab), Filter.EventuallyEq]

end TauCeti
