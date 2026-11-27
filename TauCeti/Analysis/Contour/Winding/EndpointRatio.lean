/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic

/-!
# The modulus and the argument of the winding number of a point-avoiding arc

For an absolutely continuous curve `γ` on the oriented interval with endpoints `a`, `b` that
avoids `w`, the generalized winding number `n_w(γ) = windingNumber γ a b w` exponentiates to the
endpoint ratio,

`exp (2πi · n_w(γ)) = (γ b - w) / (γ a - w)`

(`AbsolutelyContinuousOnInterval.exp_two_pi_I_mul_windingNumber`). This one identity carries the
whole polar bookkeeping of the index integral, and this file reads it off. Its modulus records the
imaginary part of the winding number,
`Im n_w(γ) = (log ‖γ a - w‖ - log ‖γ b - w‖) / 2π` — so the winding number of an *open* arc is
real exactly when its two endpoints are equidistant from `w`. Its argument records the real part
modulo `1`: `2π · Re n_w(γ) = arg (γ b - w) - arg (γ a - w)` in `Real.Angle`. Closing the curve
(`γ a = γ b`) makes the right-hand side `1`, which is the integrality of the winding number off
the curve (`AbsolutelyContinuousOnInterval.exists_int_windingNumber`).

The identity is the mod-`1` bookkeeping that Hungerbühler–Wasem Proposition 2.2 telescopes. There
a closed piecewise-`C¹` immersion `Λ` is cut at the finitely many parameters where it meets `z₀`
(`IsPwC1ImmersionOn.finite_crossings`), and the real part of the winding number of each *avoiding*
piece is pinned modulo `1` by the directions of `Λ - z₀` at the two ends of that piece —
directions that `tendsto_normalize_sub_nhdsGT` and `tendsto_normalize_sub_nhdsLT` identify with
the outgoing and reversed incoming tangents, that is with the summands of `crossingAngle`. Summing
the pieces around the closed curve is what turns the endpoint arguments into
`n_{z₀}(Λ) - Σ_ℓ crossingAngle Λ t_ℓ / 2π ∈ ℤ`; that conclusion is
`TauCeti.Contour.IsPwC1ImmersionOn.exists_int_windingNumber_eq_add_sum_crossingAngle`.

## Main results

* `AbsolutelyContinuousOnInterval.im_windingNumber` — the imaginary part of the winding number of
  an arc is the log-modulus decrement of its endpoints, over `2π`.
* `AbsolutelyContinuousOnInterval.coe_two_pi_mul_re_windingNumber` — the real part of the winding
  number, read modulo `1` as a `Real.Angle`, is the argument change between the endpoint
  directions.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Definition 2.1 and Proposition 2.2.
-/

public section

open Complex MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ}

/-- The exponent `2πi · n` of the endpoint-ratio identity has real part `-2π · Im n`. -/
private lemma re_two_pi_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I * z).re = -(2 * Real.pi * z.im) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The exponent `2πi · n` of the endpoint-ratio identity has imaginary part `2π · Re n`. -/
private lemma im_two_pi_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I * z).im = 2 * Real.pi * z.re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **The imaginary part of the winding number of an arc.** For an absolutely continuous curve `γ`
that avoids `w`,

`Im (windingNumber γ a b w) = (log ‖γ a - w‖ - log ‖γ b - w‖) / 2π`.

So the winding number of an open arc is real precisely when its endpoints are equidistant from
`w`; a closed curve is the special case where they coincide. -/
theorem _root_.AbsolutelyContinuousOnInterval.im_windingNumber
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hw : w ∉ γ '' uIcc a b) :
    (windingNumber γ a b w).im
      = (Real.log ‖γ a - w‖ - Real.log ‖γ b - w‖) / (2 * Real.pi) := by
  have hua : γ a - w ≠ 0 := sub_ne_zero.mpr fun h ↦ hw ⟨a, left_mem_uIcc, h⟩
  have hub : γ b - w ≠ 0 := sub_ne_zero.mpr fun h ↦ hw ⟨b, right_mem_uIcc, h⟩
  have h := congrArg (‖·‖) (hγ.exp_two_pi_I_mul_windingNumber hw)
  rw [Complex.norm_exp, re_two_pi_I_mul, norm_div] at h
  have hlog := congrArg Real.log h
  rw [Real.log_exp, Real.log_div (norm_ne_zero_iff.mpr hub) (norm_ne_zero_iff.mpr hua)] at hlog
  rw [eq_div_iff (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  linarith

/-- **The real part of the winding number of an arc, modulo `1`.** For an absolutely continuous
curve `γ` that avoids `w`,

`2π · Re (windingNumber γ a b w) = arg (γ b - w) - arg (γ a - w)` in `Real.Angle`,

so the real part of the winding number of an arc is determined modulo `1` by the directions of
`γ - w` at its two endpoints, while the endpoint norms determine its imaginary part. This is the
bookkeeping that telescopes around a closed curve cut at its crossings (Hungerbühler–Wasem
Proposition 2.2); the statement is an equality of `Real.Angle`s because `arg` is additive only
modulo `2π`. -/
theorem _root_.AbsolutelyContinuousOnInterval.coe_two_pi_mul_re_windingNumber
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hw : w ∉ γ '' uIcc a b) :
    ((2 * Real.pi * (windingNumber γ a b w).re : ℝ) : Real.Angle)
      = (Complex.arg (γ b - w) : Real.Angle) - (Complex.arg (γ a - w) : Real.Angle) := by
  have hua : γ a - w ≠ 0 := sub_ne_zero.mpr fun h ↦ hw ⟨a, left_mem_uIcc, h⟩
  have hub : γ b - w ≠ 0 := sub_ne_zero.mpr fun h ↦ hw ⟨b, right_mem_uIcc, h⟩
  have h := hγ.exp_two_pi_I_mul_windingNumber hw
  calc ((2 * Real.pi * (windingNumber γ a b w).re : ℝ) : Real.Angle)
      = (((2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w).im : ℝ) : Real.Angle) := by
        rw [im_two_pi_I_mul]
    _ = ((Complex.arg
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w)) : ℝ) :
            Real.Angle) := by
        rw [Complex.arg_exp, Real.Angle.coe_toIocMod]
    _ = ((Complex.arg ((γ b - w) / (γ a - w)) : ℝ) : Real.Angle) := by rw [h]
    _ = (Complex.arg (γ b - w) : Real.Angle) - (Complex.arg (γ a - w) : Real.Angle) :=
        Complex.arg_div_coe_angle hub hua

end TauCeti.Contour

end
