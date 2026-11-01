/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic

/-!
# Superposition of compound Poisson laws

A finite jump intensity `ν` determines a compound Poisson law with rate `ν univ` and
normalized jump measure `cond ν univ`. Adding two intensities convolves their laws, so jumps
in disjoint measurable regions can be separated into independent compound Poisson sums.
Zero intensity gives the point mass at zero, even though its normalized jump measure is zero.

The characteristic-function formula uses the unnormalized intensity directly. This avoids
requiring positive mass for each part when decomposing an intensity.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, chapter XVII, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-- A finite jump intensity always gives a probability law, including zero intensity. -/
theorem isProbabilityMeasure_compoundPoissonMeasure_cond
    {E : Type*} [AddMonoid E] [MeasurableSpace E]
    (ν : Measure E) [IsFiniteMeasure ν] :
    IsProbabilityMeasure (compoundPoissonMeasure (ν univ).toNNReal (cond ν univ)) := by
  by_cases hν : ν univ = 0
  · simp only [hν, ENNReal.toNNReal_zero, compoundPoissonMeasure_zero]
    infer_instance
  · let _ := cond_isProbabilityMeasure hν
    infer_instance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The characteristic exponent of a compound Poisson law is the integral of the
characteristic kernel minus one against its finite, unnormalized jump intensity. -/
theorem charFun_compoundPoissonMeasure_cond (ν : Measure E) [IsFiniteMeasure ν] (t : E) :
    charFun (compoundPoissonMeasure (ν univ).toNNReal (cond ν univ)) t =
      Complex.exp (∫ x, Complex.exp (inner ℝ x t * Complex.I) - 1 ∂ν) := by
  by_cases hν : ν univ = 0
  · have hzero : ν = 0 := Measure.measure_univ_eq_zero.mp hν
    simp [hzero]
  · let _ := cond_isProbabilityMeasure hν
    have hexp : Integrable (fun x ↦ Complex.exp (inner ℝ x t * Complex.I)) ν :=
      (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)
    rw [charFun_compoundPoissonMeasure, charFun_apply, ProbabilityTheory.cond,
      Measure.restrict_univ, integral_smul_measure, ENNReal.toReal_inv, Complex.real_smul,
      integral_sub hexp (integrable_const _), integral_const]
    simp only [ENNReal.coe_toNNReal_eq_toReal, Complex.ofReal_inv,
      Complex.real_smul, measureReal_def, mul_one]
    congr 1
    have hmass : (ν univ).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
      ⟨hν, measure_ne_top _ _⟩
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hmass),
      one_mul, mul_one]

/-- Superposition of finite jump intensities is convolution of the corresponding compound
Poisson laws. Either intensity may be zero. -/
theorem compoundPoissonMeasure_add_intensity [CompleteSpace E]
    (ν₁ ν₂ : Measure E) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    compoundPoissonMeasure ((ν₁ + ν₂) univ).toNNReal (cond (ν₁ + ν₂) univ) =
      compoundPoissonMeasure (ν₁ univ).toNNReal (cond ν₁ univ) ∗
        compoundPoissonMeasure (ν₂ univ).toNNReal (cond ν₂ univ) := by
  let _ := isProbabilityMeasure_compoundPoissonMeasure_cond ν₁
  let _ := isProbabilityMeasure_compoundPoissonMeasure_cond ν₂
  let _ := isProbabilityMeasure_compoundPoissonMeasure_cond (ν₁ + ν₂)
  apply Measure.ext_of_charFun
  funext t
  have hint (ν : Measure E) [IsFiniteMeasure ν] :
      Integrable (fun x ↦ Complex.exp (inner ℝ x t * Complex.I) - 1) ν :=
    ((integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)).sub (integrable_const _)
  simp only [charFun_conv, charFun_compoundPoissonMeasure_cond,
    integral_add_measure (hint ν₁) (hint ν₂), Complex.exp_add]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- Independent compound Poisson variables superpose by adding their finite jump intensities. -/
theorem IndepFun.hasLaw_add_compoundPoissonMeasure_cond
    {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [MeasurableSpace Ω] {P : Measure Ω}
    {ν₁ ν₂ : Measure E} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] {X Y : Ω → E}
    (hXY : IndepFun X Y P)
    (hX : HasLaw X (compoundPoissonMeasure (ν₁ univ).toNNReal (cond ν₁ univ)) P)
    (hY : HasLaw Y (compoundPoissonMeasure (ν₂ univ).toNNReal (cond ν₂ univ)) P) :
    HasLaw (X + Y)
      (compoundPoissonMeasure ((ν₁ + ν₂) univ).toNNReal (cond (ν₁ + ν₂) univ)) P := by
  let _ := isProbabilityMeasure_compoundPoissonMeasure_cond ν₁
  let _ := isProbabilityMeasure_compoundPoissonMeasure_cond ν₂
  let _ : IsFiniteMeasure P := hX.isFiniteMeasure_iff.mpr inferInstance
  rw [compoundPoissonMeasure_add_intensity]
  exact hXY.hasLaw_add hX hY

end ProbabilityTheory
