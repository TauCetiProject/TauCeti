/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.ChiSquared

/-!
# Ratios of standard Gaussian variables

This file proves that the quotient of two independent standard real Gaussian variables has the
standard Cauchy law. The measure-level identity is primary, and a `HasLaw` formulation records the
independence assumptions needed for random variables.

The denominator's square has the chi-squared law with one degree of freedom, so the corresponding
quotient by its absolute value is Student t with one degree of freedom. A measure-preserving sign
twist uses reflection invariance of the numerator to show that replacing the denominator by its
absolute value does not change the quotient law. Finally,
`studentTMeasure 1 = cauchyMeasure 0 1` identifies the result.

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
  let skew : ℝ × ℝ → ℝ × ℝ := fun z ↦
    (z.1, if z.1 < 0 then -z.2 else z.2)
  let twist : ℝ × ℝ → ℝ × ℝ := fun z ↦
    (if z.2 < 0 then -z.1 else z.1, z.2)
  let quotient : ℝ × ℝ → ℝ := fun z ↦ z.1 / z.2
  let absQuotient : ℝ × ℝ → ℝ := fun z ↦ z.1 / |z.2|
  let squareSnd : ℝ × ℝ → ℝ × ℝ := Prod.map id (fun y : ℝ ↦ y ^ 2)
  let studentRatio : ℝ × ℝ → ℝ := fun z ↦ z.1 / √(z.2 / 1)
  have hγneg : γ.map (fun x : ℝ ↦ -x) = γ := by
    simpa only [neg_zero] using gaussianReal_map_neg (μ := 0) (v := 1)
  -- Reflect the second coordinate according to the sign of the first. This skew transformation
  -- preserves the product law because every fibre transformation preserves the Gaussian law.
  have hskew : MeasurePreserving skew ρ ρ := by
    refine (MeasurePreserving.id γ).skew_product
      (g := fun y x : ℝ ↦ if y < 0 then -x else x) ?_ ?_
    · exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
        measurable_snd.neg measurable_snd
    · refine ae_of_all _ fun y ↦ ?_
      by_cases hy : y < 0
      · simpa only [hy, ↓reduceIte] using hγneg
      · simpa only [hy, ↓reduceIte] using (Measure.map_id' (μ := γ))
  -- Conjugating the skew map by coordinate swaps reflects the numerator exactly when the
  -- denominator is negative.
  have htwist : MeasurePreserving twist ρ ρ := by
    have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) ρ ρ :=
      Measure.measurePreserving_swap
    have htwist_eq : twist = (Prod.swap : ℝ × ℝ → ℝ × ℝ) ∘ skew ∘ Prod.swap := by
      funext z
      rfl
    rw [htwist_eq]
    exact hswap.comp (hskew.comp hswap)
  have hquotient : ρ.map quotient = ρ.map absQuotient := by
    calc
      ρ.map quotient = (ρ.map twist).map quotient := by rw [htwist.map_eq]
      _ = ρ.map (quotient ∘ twist) := by
        rw [Measure.map_map (by fun_prop) htwist.measurable]
      _ = ρ.map absQuotient := by
        apply Measure.map_congr
        refine ae_of_all _ fun z ↦ ?_
        by_cases hz : z.2 < 0
        · simp only [quotient, twist, absQuotient, hz, ↓reduceIte, Function.comp_apply,
            abs_of_neg hz]
          ring
        · simp only [quotient, twist, absQuotient, hz, ↓reduceIte, Function.comp_apply,
            abs_of_nonneg (le_of_not_gt hz)]
  -- Squaring the denominator turns its Gaussian law into `chiSquaredMeasure 1`, putting the
  -- absolute-value quotient in the exact form of the existing Student t ratio theorem.
  have hsquareSnd : ρ.map squareSnd = γ.prod (chiSquaredMeasure 1) := by
    rw [← Measure.map_prod_map γ γ measurable_id (by fun_prop), Measure.map_id,
      gaussianReal_map_sq]
  calc
    ρ.map quotient = ρ.map absQuotient := hquotient
    _ = (ρ.map squareSnd).map studentRatio := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply congrArg (fun f : ℝ × ℝ → ℝ ↦ ρ.map f)
      funext z
      simp only [studentRatio, squareSnd, absQuotient, Function.comp_apply, Prod.map_apply',
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
