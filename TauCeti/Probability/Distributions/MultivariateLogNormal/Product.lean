/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MultivariateLogNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Sum

/-!
# Products of independent multivariate log-normal vectors

Componentwise multiplication of independent multivariate log-normal vectors adds their log-means
and log-covariances. Both the product-measure pushforward and the random-variable form are proved
here, including singular and zero covariances and empty coordinate types.

The underlying construction is coordinatewise exponentiation of a Gaussian sum, using
`multivariateLogNormalMeasure_def`, `multivariateGaussian_conv_multivariateGaussian`, and
Mathlib's `Measure.map_prod_map`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The componentwise product of independent log-normal vectors adds their Gaussian parameters.
The covariances need only be positive semidefinite. -/
@[simp]
theorem map_mul_prod_multivariateLogNormalMeasure (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef) :
    ((multivariateLogNormalMeasure m₁ S₁).prod
        (multivariateLogNormalMeasure m₂ S₂)).map
        (fun z ↦ WithLp.toLp 2 (fun i ↦ z.1 i * z.2 i)) =
      multivariateLogNormalMeasure (m₁ + m₂) (S₁ + S₂) := by
  simp only [multivariateLogNormalMeasure_def]
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop),
    ← multivariateGaussian_conv_multivariateGaussian m₁ m₂ hS₁ hS₂,
    Measure.conv, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  ext i
  simp [Real.exp_add]

end TauCeti.Probability

namespace ProbabilityTheory.IndepFun

open TauCeti.Probability

/-- Independent multivariate log-normal random vectors multiply componentwise by adding their
log-means and log-covariances, including singular covariances. -/
theorem hasLaw_mul_multivariateLogNormalMeasure {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] {P : Measure Ω} {X Y : Ω → EuclideanSpace ℝ ι}
    {m₁ m₂ : EuclideanSpace ℝ ι} {S₁ S₂ : Matrix ι ι ℝ}
    (hXY : IndepFun X Y P) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hX : HasLaw X (multivariateLogNormalMeasure m₁ S₁) P)
    (hY : HasLaw Y (multivariateLogNormalMeasure m₂ S₂) P) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun i ↦ X ω i * Y ω i))
      (multivariateLogNormalMeasure (m₁ + m₂) (S₁ + S₂)) P := by
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hmul : HasLaw
      (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
        WithLp.toLp 2 (fun i ↦ z.1 i * z.2 i))
      (multivariateLogNormalMeasure (m₁ + m₂) (S₁ + S₂))
      ((multivariateLogNormalMeasure m₁ S₁).prod (multivariateLogNormalMeasure m₂ S₂)) :=
    ⟨by fun_prop, map_mul_prod_multivariateLogNormalMeasure m₁ m₂ hS₁ hS₂⟩
  exact hmul.fun_comp (hXY.hasLaw_prod hX hY)

end ProbabilityTheory.IndepFun
