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
import TauCeti.Analysis.SpecialFunctions.Exp.Modular

/-!
# Weak lower semicontinuity of the reduced vortex potential

Subtracting the background amplitude `-log(1 + |P|²)/2` from the prescribed-zero scalar
vortex equation gives the potential

`∫ (|P|² / (1 + |P|²)) (exp(2w) - 1 - 2w)`.

This file treats it as an extended nonnegative integral on real `Lᵖ` with `1 ≤ p`, for any
measure and any a.e.-measurable weight in place of `|P|² / (1 + |P|²)`, where it is weakly lower
semicontinuous, including at functions where it is infinite. For the polynomial weight and
Lebesgue measure on the plane it is finite on continuous compactly supported corrections. Thus
passage to a weak limit does not lose the nonlinear potential in the variational existence argument
(`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`).

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

/-- The nonlinear potential `∫ h (exp(2u) - 1 - 2u)` of the background-subtracted vortex equation
is weakly lower semicontinuous on real `Lᵖ(α, μ)` for `1 ≤ p`, for every measure `μ` against which
both the `Lᵖ` space and the potential are taken, and every a.e.-measurable real weight `h`. Where
`h` is negative the integrand is cut off at zero by `ENNReal.ofReal`. No integrability assumption
on the potential is needed. The vortex equation with zero divisor `P` uses `α = ℂ`, `p = 2` and
the weight `h = ‖P‖² / (1 + ‖P‖²)`. -/
theorem lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] {h : α → ℝ} (hh : AEMeasurable h μ) :
    LowerSemicontinuous (fun u : WeakSpace ℝ (Lp ℝ p μ) ↦
      ∫⁻ z, ENNReal.ofReal (h z *
        (Real.exp (2 * ((toWeakSpace ℝ (Lp ℝ p μ)).symm u z)) - 1 -
          2 * ((toWeakSpace ℝ (Lp ℝ p μ)).symm u z))) ∂μ) := by
  let Φ : ℝ → ℝ := fun t ↦ Real.exp (2 * t) - 1 - 2 * t
  have hΦ : Continuous Φ := by dsimp [Φ]; fun_prop
  have hconv : ConvexOn ℝ univ Φ := by
    have hlin := (LinearMap.mulLeft ℝ (2 : ℝ)).concaveOn (convex_univ : Convex ℝ (univ : Set ℝ))
    simpa only [preimage_univ, Pi.sub_def, Function.comp_def, LinearMap.mulLeft_apply, Φ] using
      ((convexOn_exp.comp_linearMap (LinearMap.mulLeft ℝ (2 : ℝ))).sub
        (concaveOn_const (1 : ℝ) convex_univ)).sub hlin
  have heq (u : Lp ℝ p μ) :
      (∫⁻ z, ENNReal.ofReal (Φ (u z)) ∂(μ.withDensity (fun z ↦ ENNReal.ofReal (h z)))) =
        ∫⁻ z, ENNReal.ofReal (h z * Φ (u z)) ∂μ := by
    have hmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (Φ (u z))) μ :=
      aemeasurable_ofReal_comp_Lp Measure.AbsolutelyContinuous.rfl hΦ u
    rw [lintegral_withDensity_eq_lintegral_mul₀ hh.ennreal_ofReal hmeas]
    apply lintegral_congr
    intro z
    rw [ENNReal.ofReal_mul' (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _), Pi.mul_apply]
  have hlsc := lowerSemicontinuous_lintegral_ofReal_comp_toWeakSpace_symm (p := p)
    (withDensity_absolutelyContinuous μ (fun z ↦ ENNReal.ofReal (h z))) hΦ hconv
  simpa only [heq, Φ] using hlsc

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
