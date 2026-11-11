/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf
public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Dawson's integral

This file defines Dawson's integral as an entire function,

$$
F(z) = e^{-z^2} \int_0^1 z\, e^{(sz)^2}\, ds,
$$

that is `e^{−z²} ∫₀^z e^{t²} dt` along the straight segment from `0` to `z` (DLMF 7.2.5).
It proves that `F` is entire with `F′ = 1 − 2zF`, that `F(0) = 0` and `F` is odd, and that
`F(iy) = i (√π/2) e^{y²} erf y` on the imaginary axis.

## Main declarations

* `TauCeti.dawson`: Dawson's integral `F`.
* `TauCeti.hasDerivAt_dawson`, `TauCeti.differentiable_dawson`: `F′ = 1 − 2zF`, and `F` is
  entire.
* `TauCeti.dawson_zero`, `TauCeti.dawson_neg`: `F(0) = 0` and `F(−z) = −F(z)`.
* `TauCeti.dawson_mul_I`: `F(iy) = i (√π/2) e^{y²} erf y` for real `y`, with
  `TauCeti.Real.erf`.

## Implementation notes

The segment integral `z ∫₀¹ f(sz) ds` of an entire function `f` is `g(z) − g(0)` for any
primitive `g` of `f`, by the fundamental theorem of calculus along the segment. A primitive
exists by Mathlib's `Differentiable.isExactOn_univ`, so the segment integral is a primitive of
`f`. This gives `F′` without differentiating under the integral sign.

The segment-primitive lemmas are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file
`DLMFMathlib/Analysis/Complex/SegmentPrimitive.lean`.
-/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory

open scoped Real

namespace TauCeti

/-- Integrating a complex derivative along the straight segment from `0` to `z` recovers the
endpoint difference. -/
private theorem mul_integral_comp_mul_eq_sub {f g : ℂ → ℂ}
    (hg : ∀ z, HasDerivAt g (f z) z) (z : ℂ) :
    z * (∫ t : ℝ in 0..1, f (t * z)) = g z - g 0 := by
  have hgd : Differentiable ℂ g := fun w => (hg w).differentiableAt
  have he : deriv g = f := funext fun w => (hg w).deriv
  have hf : Continuous f := he ▸ hgd.deriv.continuous
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => g (u * z)) (z * f (t * z)) t := by
    simpa [mul_comm] using
      ((hg (t * z)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const z)).comp_ofReal
  have hi : IntervalIntegrable (fun t : ℝ => z * f (t * z)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => z * f (t * z))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa [intervalIntegral.integral_const_mul] using h

/-- The straight-segment integral `w ↦ w ∫₀¹ f(tw) dt` of an entire function `f` is a primitive
of `f`. -/
private theorem hasDerivAt_mul_integral_comp_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z : ℂ) : HasDerivAt (fun w : ℂ => w * (∫ t : ℝ in 0..1, f (t * w))) (f z) z := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hg' (w : ℂ) := hg w (mem_univ w)
  have he : (fun w : ℂ => w * (∫ t : ℝ in 0..1, f (t * w))) = fun w => g w - g 0 :=
    funext (mul_integral_comp_mul_eq_sub hg')
  rw [he]
  exact (hg' z).sub_const _

/-- **Dawson's integral** `F(z) = e^{−z²} ∫₀¹ z e^{(sz)²} ds`, the integral
`e^{−z²} ∫₀^z e^{t²} dt` taken along the straight segment from `0` to `z` (DLMF 7.2.5). -/
def dawson (z : ℂ) : ℂ :=
  exp (-z ^ 2) * ∫ s in (0 : ℝ)..1, z * exp (((s : ℂ) * z) ^ 2)

/-- Dawson's integral with the factor `z` taken out of the integral. -/
theorem dawson_eq (z : ℂ) :
    dawson z = exp (-z ^ 2) * (z * ∫ s in (0 : ℝ)..1, exp (((s : ℂ) * z) ^ 2)) := by
  rw [dawson, intervalIntegral.integral_const_mul]

/-- **The differential equation of Dawson's integral** (DLMF 7.10.1 for `F`):
`F′(z) = 1 − 2zF(z)`. -/
theorem hasDerivAt_dawson (z : ℂ) : HasDerivAt dawson (1 - 2 * z * dawson z) z := by
  have hG := hasDerivAt_mul_integral_comp_mul
    (f := fun u : ℂ => exp (u ^ 2)) (by fun_prop) z
  have hE : HasDerivAt (fun w : ℂ => exp (-w ^ 2)) (exp (-z ^ 2) * (-(2 * z))) z := by
    have h := ((hasDerivAt_pow 2 z).neg).cexp
    simpa [mul_comm] using h
  have h := hE.mul hG
  have heq : ((fun w : ℂ => exp (-w ^ 2)) * fun w : ℂ => w * ∫ t : ℝ in 0..1, exp ((t * w) ^ 2)) =
      dawson := funext fun w => (dawson_eq w).symm
  rw [heq] at h
  convert h using 1
  rw [dawson_eq, show exp (-z ^ 2) * exp (z ^ 2) = 1 by rw [← exp_add]; simp]
  ring

/-- Dawson's integral is entire. -/
theorem differentiable_dawson : Differentiable ℂ dawson :=
  fun z => (hasDerivAt_dawson z).differentiableAt

/-- `F′ = 1 − 2zF` as an equation for `deriv`. -/
theorem deriv_dawson (z : ℂ) : deriv dawson z = 1 - 2 * z * dawson z :=
  (hasDerivAt_dawson z).deriv

/-- `F(0) = 0`. -/
@[simp]
theorem dawson_zero : dawson 0 = 0 := by
  simp [dawson]

/-- Dawson's integral is odd: `F(−z) = −F(z)`. -/
theorem dawson_neg (z : ℂ) : dawson (-z) = -dawson z := by
  simp only [dawson_eq, neg_sq, mul_neg, neg_mul]

/-- **Dawson's integral on the imaginary axis**: `F(iy) = i (√π/2) e^{y²} erf y` for real `y`,
with `TauCeti.Real.erf`. -/
theorem dawson_mul_I (y : ℝ) :
    dawson (y * I) = I * (√π / 2 : ℝ) * Real.exp (y ^ 2) * (Real.erf y : ℂ) := by
  have hint : (∫ s in (0 : ℝ)..1, ((y : ℂ) * I) * exp (((s : ℂ) * (y * I)) ^ 2)) =
      I * ((∫ t in (0 : ℝ)..y, Real.exp (-t ^ 2) : ℝ) : ℂ) := by
    have hpt : ∀ s : ℝ, ((y : ℂ) * I) * exp (((s : ℂ) * (y * I)) ^ 2) =
        I * ((y * Real.exp (-(s * y) ^ 2) : ℝ) : ℂ) := fun s => by
      have : ((s : ℂ) * (y * I)) ^ 2 = ((-(s * y) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring_nf
        rw [I_sq]
        ring
      rw [this, ← ofReal_exp]
      push_cast
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul]
    congr 2
    have h := intervalIntegral.smul_integral_comp_mul_right (fun t => Real.exp (-t ^ 2)) y
      (a := 0) (b := 1)
    simpa only [smul_eq_mul, zero_mul, one_mul] using h
  have hsq : -((y : ℂ) * I) ^ 2 = ((y ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hpi : (√π : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  rw [dawson, hint, hsq, ← ofReal_exp, Real.erf_def]
  push_cast
  field_simp

end TauCeti
