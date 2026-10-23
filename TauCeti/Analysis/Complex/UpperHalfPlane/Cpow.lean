/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
-- Non-public: the logarithmic derivative of a principal power is used only in a proof.
import TauCeti.Analysis.SpecialFunctions.Pow.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Principal powers of `z - x` on the upper half-plane

For a real number `x`, the difference `z - x` of an upper-half-plane point and `x` again has
positive imaginary part, hence lies in `Complex.slitPlane`.  The principal power
`(z - x) ^ (r : ℂ)` is therefore holomorphic and nonvanishing there, and its logarithmic
derivative is the simple fraction `r / (z - x)`.

Negating the base, replacing `z - x` by `x - z`, multiplies the power by the constant
`exp (π r i)` -- unimodular when `r` is real -- because the two bases lie on opposite sides of the
real axis.

Principal powers also commute with division of two upper-half-plane points: their arguments
differ by less than `π`, so their quotient introduces no branch jump.

These are the basic branch facts for a factor of a product of principal powers with real base
points, such as the Schwarz--Christoffel integrand.

## Main results

* `TauCeti.sub_ofReal_mem_slitPlane_of_im_pos`
* `TauCeti.differentiableAt_sub_cpow_of_im_pos`
* `TauCeti.sub_cpow_ne_zero_of_im_pos`
* `TauCeti.sub_cpow_eq_exp_mul_sub_cpow_of_im_pos`
* `TauCeti.logDeriv_sub_cpow_of_im_pos`
* `TauCeti.div_cpow_of_im_pos`
-/

public section

open Complex

namespace TauCeti

/-- Principal complex powers commute with division when both bases have positive imaginary
part. Their arguments differ by less than `π`, so the quotient introduces no branch jump. -/
lemma div_cpow_of_im_pos {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) (r : ℂ) :
    (x / y) ^ r = x ^ r / y ^ r := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have hlog : Complex.log (x / y) = Complex.log x - Complex.log y := by
    apply Complex.ext
    · simp only [Complex.log_re, norm_div, Complex.sub_re]
      exact Real.log_div (norm_ne_zero_iff.mpr hx0) (norm_ne_zero_iff.mpr hy0)
    · simp only [Complex.log_im, Complex.sub_im]
      exact Complex.arg_div_of_im_pos hx hy
  rw [Complex.cpow_def_of_ne_zero (div_ne_zero hx0 hy0), hlog, sub_mul,
    Complex.exp_sub, Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hy0]

/-- Translating a point with positive imaginary part by a real number leaves it in the slit
plane. -/
lemma sub_ofReal_mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    z - (x : ℂ) ∈ slitPlane := by
  simp [slitPlane, hz.ne']

/-- The principal power `(z - x) ^ (r : ℂ)` with real base point `x` and real exponent `r` is
differentiable at every point with positive imaginary part. -/
lemma differentiableAt_sub_cpow_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    DifferentiableAt ℂ (fun w : ℂ => (w - (x : ℂ)) ^ (r : ℂ)) z :=
  (differentiableAt_id.sub_const (x : ℂ)).cpow_const
    (sub_ofReal_mem_slitPlane_of_im_pos hz x)

/-- The principal power `(z - x) ^ (r : ℂ)` with real base point `x` and real exponent `r` does
not vanish at a point with positive imaginary part. -/
lemma sub_cpow_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    (z - (x : ℂ)) ^ (r : ℂ) ≠ 0 := by
  rw [Complex.cpow_ne_zero_iff]
  left
  intro h
  have := congr_arg Complex.im h
  simp only [sub_im, ofReal_im, sub_zero, zero_im] at this
  exact hz.ne' this

/-- Negating the base of a principal power with real base point multiplies it by the factor
`exp (π r i)`, unimodular for a real exponent `r`.  At a point with positive imaginary part the two
bases `z - x` and `x - z` lie on opposite sides of the real axis, so their arguments differ by `π`
and neither meets the branch cut of the other. -/
lemma sub_cpow_eq_exp_mul_sub_cpow_of_im_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) (r : ℂ) :
    (z - (x : ℂ)) ^ r = Complex.exp ((Real.pi : ℂ) * r * I) * ((x : ℂ) - z) ^ r := by
  have him : ((x : ℂ) - z).im < 0 := by simpa using hz
  have hne : (x : ℂ) - z ≠ 0 := fun h => by simp [h] at him
  have hlog : ∀ w : ℂ, w.im < 0 → Complex.log (-w) = Complex.log w + (Real.pi : ℂ) * I := by
    intro w hw
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]
  have hneg : z - (x : ℂ) = -((x : ℂ) - z) := by ring
  rw [hneg, Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr hne),
    Complex.cpow_def_of_ne_zero hne, hlog _ him, ← Complex.exp_add]
  congr 1
  ring

/-- The logarithmic derivative of `w ↦ (w - x) ^ (r : ℂ)` at a point with positive imaginary
part is the simple fraction `r / (z - x)`. -/
lemma logDeriv_sub_cpow_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    logDeriv (fun w : ℂ => (w - (x : ℂ)) ^ (r : ℂ)) z = (r : ℂ) / (z - (x : ℂ)) := by
  rw [logDeriv_fun_cpow (f := fun w : ℂ => w - (x : ℂ)) (by fun_prop)
    (sub_ofReal_mem_slitPlane_of_im_pos hz x), logDeriv_apply, deriv_sub_const, deriv_id'',
    mul_one_div]

end TauCeti

end
