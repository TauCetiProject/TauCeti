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
For any intensity `ν` and set `s`, the rate `(ν s).toNNReal` and jump law `cond ν s` give a
probability law (`isProbabilityMeasure_compoundPoissonMeasure_cond`): when `ν s` is zero or
infinite, `(ν s).toNNReal` vanishes and the law is the point mass at zero.

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

/-- The rate `(ν s).toNNReal` and jump law `cond ν s` of any intensity `ν` on any set `s` give a
probability law. When `ν s` is zero or infinite, `(ν s).toNNReal = 0` and the law is the point
mass at zero; otherwise `cond ν s` is a probability measure. -/
instance isProbabilityMeasure_compoundPoissonMeasure_cond
    {E : Type*} [AddMonoid E] [MeasurableSpace E] (ν : Measure E) (s : Set E) :
    IsProbabilityMeasure (compoundPoissonMeasure (ν s).toNNReal (cond ν s)) := by
  by_cases h : ν s = 0 ∨ ν s = ∞
  · rcases h with h | h <;> simp only [h, ENNReal.toNNReal_zero, ENNReal.toNNReal_top,
      compoundPoissonMeasure_zero] <;> infer_instance
  · rw [not_or] at h
    let _ := cond_isProbabilityMeasure_of_finite h.1 h.2
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
      integrable_exp_inner_mul_I t
    have hmass : (ν univ).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
      ⟨hν, measure_ne_top _ _⟩
    rw [charFun_compoundPoissonMeasure]
    congr 1
    simp only [ENNReal.coe_toNNReal_eq_toReal, ProbabilityTheory.cond, Measure.restrict_univ,
      charFun_apply, integral_smul_measure, ENNReal.toReal_inv, Complex.real_smul,
      Complex.ofReal_inv, integral_sub hexp (integrable_const _), integral_const,
      measureReal_def, mul_one]
    -- Treat the kernel integral as a scalar during normalization.
    generalize (∫ x, Complex.exp (inner ℝ x t * Complex.I) ∂ν) = z
    field_simp [Complex.ofReal_ne_zero.mpr hmass]

/-- Superposition of finite jump intensities is convolution of the corresponding compound
Poisson laws. Either intensity may be zero. -/
theorem compoundPoissonMeasure_add_intensity [CompleteSpace E]
    (ν₁ ν₂ : Measure E) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    compoundPoissonMeasure ((ν₁ + ν₂) univ).toNNReal (cond (ν₁ + ν₂) univ) =
      compoundPoissonMeasure (ν₁ univ).toNNReal (cond ν₁ univ) ∗
        compoundPoissonMeasure (ν₂ univ).toNNReal (cond ν₂ univ) := by
  apply Measure.ext_of_charFun
  funext t
  have hint (ν : Measure E) [IsFiniteMeasure ν] :
      Integrable (fun x ↦ Complex.exp (inner ℝ x t * Complex.I) - 1) ν :=
    (integrable_exp_inner_mul_I t).sub (integrable_const _)
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
  let _ : IsFiniteMeasure P := hX.isFiniteMeasure_iff.mpr inferInstance
  rw [compoundPoissonMeasure_add_intensity]
  exact hXY.hasLaw_add hX hY

end ProbabilityTheory
