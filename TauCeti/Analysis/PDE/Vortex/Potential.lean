/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Weak lower semicontinuity of the reduced vortex potential

Subtracting the background amplitude `-log(1 + |P|²)/2` from the prescribed-zero scalar
vortex equation gives the potential

`∫ (|P|² / (1 + |P|²)) (exp(2w) - 1 - 2w)`.

This file treats it as an extended nonnegative integral on real `L²(ℂ)`. It is weakly lower
semicontinuous, including at functions where it is infinite, and finite on continuous
compactly supported corrections. Thus passage to a weak limit does not lose the nonlinear
potential in the variational existence argument. No minimizer or solution is constructed here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Vortex

/-- The nonlinear potential of the background-subtracted vortex equation is weakly lower
semicontinuous on real `L²(ℂ)`. No monicity, degree, or integrability assumption on the
polynomial or on the potential is needed. -/
theorem lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub (P : Polynomial ℂ) :
    LowerSemicontinuous (fun u : WeakSpace ℝ (Lp ℝ 2 (volume : Measure ℂ)) ↦
      ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * ((toWeakSpace ℝ (Lp ℝ 2 (volume : Measure ℂ))).symm u z)) - 1 -
          2 * ((toWeakSpace ℝ (Lp ℝ 2 (volume : Measure ℂ))).symm u z)))) := by
  let h : ℂ → ℝ := fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2)
  let Φ : ℝ → ℝ := fun t ↦ Real.exp (2 * t) - 1 - 2 * t
  have hh : Continuous h := by dsimp [h]; fun_prop (disch := intro z; positivity)
  have hΦ : Continuous Φ := by dsimp [Φ]; fun_prop
  have hconv : ConvexOn ℝ univ Φ := by
    have hlin := (LinearMap.mulLeft ℝ (2 : ℝ)).concaveOn (convex_univ : Convex ℝ (univ : Set ℝ))
    simpa only [preimage_univ, Pi.sub_def, Function.comp_def, LinearMap.mulLeft_apply, Φ] using
      ((convexOn_exp.comp_linearMap (LinearMap.mulLeft ℝ (2 : ℝ))).sub
        (concaveOn_const (1 : ℝ) convex_univ)).sub hlin
  have heq (u : Lp ℝ 2 (volume : Measure ℂ)) :
      (∫⁻ z, ENNReal.ofReal (Φ (u z)) ∂(volume.withDensity (fun z ↦ ENNReal.ofReal (h z)))) =
        ∫⁻ z, ENNReal.ofReal (h z * Φ (u z)) := by
    have hmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (Φ (u z))) volume :=
      aemeasurable_ofReal_comp_Lp Measure.AbsolutelyContinuous.rfl hΦ u
    rw [lintegral_withDensity_eq_lintegral_mul₀ hh.aemeasurable.ennreal_ofReal hmeas]
    apply lintegral_congr
    intro z
    rw [ENNReal.ofReal_mul (by dsimp [h]; positivity), Pi.mul_apply]
  have hlsc := lowerSemicontinuous_lintegral_ofReal_comp_toWeakSpace_symm (p := 2)
    (withDensity_absolutelyContinuous volume (fun z ↦ ENNReal.ofReal (h z))) hΦ hconv
  simpa only [heq, h, Φ] using hlsc

/-- Continuous compactly supported corrections have finite nonlinear vortex potential.
This supplies a finite-potential domain for the extended functional. -/
theorem integrable_mul_exp_sub_one_sub (P : Polynomial ℂ) {w : ℂ → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) :
    Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * w z) - 1 - 2 * w z)) := by
  have hcont : Continuous (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * w z) - 1 - 2 * w z)) := by fun_prop (disch := intro z; positivity)
  apply hcont.integrable_of_hasCompactSupport
  apply hc.mono
  intro z hz hwz
  apply hz
  simp [hwz]

end TauCeti.Vortex
