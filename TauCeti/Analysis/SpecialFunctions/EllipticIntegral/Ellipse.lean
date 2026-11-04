/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
public import TauCeti.Analysis.Green.Examples.CurveArea.Ellipse
import TauCeti.MeasureTheory.Function.MetricDerivative.Variation

/-!
# The perimeter of an ellipse

The angular parametrization `ellipse a b t = a cos t + b sin t I` has length
`4 * a * legendreEc (√(1 - b²/a²))` when `a` is its positive major semiaxis.
The length is the metric total variation, not merely an unevaluated speed integral.
The formula also allows a zero or negative minor semiaxis: reversing one axis does not
change length, and a degenerate ellipse traverses its segment twice.

The speed integral is evaluated by the incomplete second-kind integral after a quarter-turn
of the angular coordinate. Its quasi-periodicity gives the full perimeter.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Example 9.4-1.
* Bastiaan J Braams, `lean-codes`, `Carlson/Elliptic/Applications.lean` at commit `2b8cba1`,
  `Carlson.ellipse_perimeter` (Apache-2.0), proves the corresponding speed-integral formula
  using Carlson's symmetric integrals. Here the direct Legendre integrals and metric
  variation identify the length of the parametrized curve.
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti.Green.Examples

open TauCeti.Real

private theorem norm_deriv_ellipse_eq_legendreE_integrand {a b : ℝ}
    (ha : 0 < a) (hba : b ^ 2 ≤ a ^ 2) (t : ℝ) :
    ‖deriv (ellipse a b) t‖ =
      a * (1 - (√(1 - b ^ 2 / a ^ 2)) ^ 2 * Real.sin (π / 2 - t) ^ 2) ^ (1 / 2 : ℝ) := by
  have he : 0 ≤ 1 - b ^ 2 / a ^ 2 := by
    exact sub_nonneg.mpr ((div_le_one (sq_pos_of_pos ha)).mpr hba)
  rw [(hasDerivAt_ellipse a b t).deriv, Complex.norm_add_mul_I,
    Real.sq_sqrt he, Real.sin_pi_div_two_sub, ← Real.sqrt_eq_rpow]
  have hrad : (-a * Real.sin t) ^ 2 + (b * Real.cos t) ^ 2 =
      a ^ 2 * (1 - (1 - b ^ 2 / a ^ 2) * Real.cos t ^ 2) := by
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hrad, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

/-- The integrated speed of one angular traversal of an ellipse is `4aE(e)`.
The major semiaxis is positive; the other axis may have either sign or vanish. -/
theorem integral_norm_deriv_ellipse {a b : ℝ} (ha : 0 < a) (hba : b ^ 2 ≤ a ^ 2) :
    (∫ t in (0 : ℝ)..2 * π, ‖deriv (ellipse a b) t‖) =
      4 * a * legendreEc (√(1 - b ^ 2 / a ^ 2)) := by
  let e := √(1 - b ^ 2 / a ^ 2)
  have hspeed : Continuous (fun t => ‖deriv (ellipse a b) t‖) := by
    simp_rw [(hasDerivAt_ellipse a b _).deriv]
    fun_prop
  have hprim (t : ℝ) : HasDerivAt (fun t => -a * legendreE (π / 2 - t) e)
      ‖deriv (ellipse a b) t‖ t := by
    convert ((hasDerivAt_legendreE e (π / 2 - t)).comp t
      ((hasDerivAt_id t).const_sub (π / 2))).const_mul (-a) using 1
    · rfl
    · rw [norm_deriv_ellipse_eq_legendreE_integrand ha hba]
      dsimp only [e]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim t)
    (hspeed.intervalIntegrable _ _)]
  have hend : legendreE (π / 2 - 2 * π) e = -3 * legendreEc e := by
    have harg : π / 2 - 2 * π = π / 2 + (-2 : ℤ) * π := by norm_num; ring
    rw [harg, legendreE_add_int_mul_pi, ← legendreEc_def]
    norm_num
    ring
  rw [sub_zero, hend, ← legendreEc_def]
  ring

/-- The perimeter of an ellipse, as metric total variation, is `4aE(e)`.
This includes the circle and the twice-traversed segment when the minor axis is zero. -/
theorem eVariationOn_ellipse {a b : ℝ} (ha : 0 < a) (hba : b ^ 2 ≤ a ^ 2) :
    eVariationOn (ellipse a b) (Icc 0 (2 * π)) =
      ENNReal.ofReal (4 * a * legendreEc (√(1 - b ^ 2 / a ^ 2))) := by
  have hAC := absolutelyContinuous_ellipse a b
  have hlength := hAC.integral_norm_deriv_eq_eVariationOn_toReal Real.two_pi_pos.le
  rw [uIcc_of_le Real.two_pi_pos.le, integral_norm_deriv_ellipse ha hba] at hlength
  have hfinite : eVariationOn (ellipse a b) (Icc 0 (2 * π)) ≠ ⊤ := by
    simpa only [BoundedVariationOn, uIcc_of_le Real.two_pi_pos.le] using hAC.boundedVariationOn
  rw [hlength, ENNReal.ofReal_toReal hfinite]

end TauCeti.Green.Examples
