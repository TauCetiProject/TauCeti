/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.ChiSquared
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Ratios of standard Gaussian variables

This file proves that the quotient of two independent standard real Gaussian variables has the
standard Cauchy law. The measure-level identity is primary, and a `HasLaw` formulation records the
independence assumptions needed for random variables.

Ratios of independent standard Gaussian variables provide a standard construction of Cauchy random
variables. The measure identity is useful for distributional calculations on product spaces, while
the `HasLaw` theorem lets probabilistic arguments recognize a quotient of independent standard
Gaussians as Cauchy.

## Main results

* `TauCeti.Probability.map_div_prod_gaussianReal` -- mapping the product of two standard Gaussian
  measures under division gives the standard Cauchy measure;
* `TauCeti.Probability.hasLaw_ratio_gaussian_cauchy` -- the corresponding random-variable theorem.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti

namespace Probability

/-- Mapping the product of two standard Gaussian measures under division gives the standard
Cauchy measure. -/
@[simp]
theorem map_div_prod_gaussianReal :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun z : ℝ × ℝ ↦ z.1 / z.2) =
      cauchyMeasure 0 1 := by
  let γ := gaussianReal 0 1
  let ρ := γ.prod γ
  let squareSnd : ℝ × ℝ → ℝ × ℝ := Prod.map id (fun y : ℝ ↦ y ^ 2)
  let studentRatio : ℝ × ℝ → ℝ := fun z ↦ z.1 / √(z.2 / 1)
  have hγneg : γ.map (fun x : ℝ ↦ -x) = γ := by
    simpa only [neg_zero] using gaussianReal_map_neg (μ := 0) (v := 1)
  have hquotient := Measure.map_div_prod_eq_map_div_abs (ν := γ) hγneg
  -- Squaring the denominator turns its Gaussian law into `chiSquaredMeasure 1`, putting the
  -- absolute-value quotient in the exact form of the existing Student t ratio theorem.
  have hsquareSnd : ρ.map squareSnd = γ.prod (chiSquaredMeasure 1) := by
    rw [← Measure.map_prod_map γ γ measurable_id (by fun_prop), Measure.map_id,
      gaussianReal_map_sq]
  calc
    ρ.map (fun z : ℝ × ℝ ↦ z.1 / z.2) = ρ.map (fun z : ℝ × ℝ ↦ z.1 / |z.2|) := hquotient
    _ = (ρ.map squareSnd).map studentRatio := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply congrArg (fun f : ℝ × ℝ → ℝ ↦ ρ.map f)
      funext z
      simp only [studentRatio, squareSnd, Function.comp_apply, Prod.map_apply',
        id_eq, div_one, Real.sqrt_sq_eq_abs]
    _ = (γ.prod (chiSquaredMeasure 1)).map studentRatio := by rw [hsquareSnd]
    _ = studentTMeasure 1 := map_div_sqrt_chiSquaredMeasure one_pos
    _ = cauchyMeasure 0 1 := studentTMeasure_one

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ}

/-- If `X` and `Y` are independent standard Gaussian variables, then `X / Y` has the standard
Cauchy law. -/
theorem hasLaw_ratio_gaussian_cauchy (hXY : IndepFun X Y P)
    (hX : HasLaw X (gaussianReal 0 1) P) (hY : HasLaw Y (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ X ω / Y ω) (cauchyMeasure 0 1) P := by
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hpair : HasLaw (fun ω ↦ (X ω, Y ω))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) P := hXY.hasLaw_prod hX hY
  have hratio : HasLaw (fun z : ℝ × ℝ ↦ z.1 / z.2) (cauchyMeasure 0 1)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ⟨by fun_prop, map_div_prod_gaussianReal⟩
  exact hratio.fun_comp hpair

end Probability

end TauCeti
