/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import TauCeti.MeasureTheory.Measure.PiWithDensity
public import TauCeti.Probability.Distributions.Gaussian.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The standard Gaussian measure on a finite product

The product measure `γ^ι = Measure.pi (fun _ : ι => gaussianReal 0 1)` is Lebesgue measure on
`ℝ^ι` weighted by the joint density `x ↦ ∏ i, gaussianPDFReal 0 1 (x i)`. That identification is
what lets a weight-in-the-measure statement about `γ^ι` be read as a weight-in-the-function
statement about `volume^ι`, via `TauCeti.weightL2Isometry`.

Like `TauCeti.Probability.gaussianPDFReal_zero_one`, these are statements about the Gaussian
distribution
alone (no orthogonal family appears), so they live here rather than with the multi-index Hermite
basis that consumes them.

## Main statements

* `TauCeti.Probability.prod_gaussianPDFReal_zero_one`: the joint density in closed form,
  `(2π)^(-d/2) · e^{-∑ᵢ xᵢ²/2}`, where `d` is the number of coordinates.
* `TauCeti.Probability.pi_gaussianReal_eq_withDensity`: `γ^ι = volume^ι` weighted by the joint
  density.
* `TauCeti.Probability.pi_volume_absolutelyContinuous_pi_gaussianReal`: the joint density never
  vanishes, so
  `volume^ι`-null sets are exactly `γ^ι`-null sets in the direction one needs to move an
  almost-everywhere statement from `γ^ι` to `volume^ι`.
* `ProbabilityTheory.isGaussian_pi`: a finite product of Gaussian measures is Gaussian. In
  particular `γ^ι` is Gaussian, so the Gaussian moment and integrability API applies to it.
-/

public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

namespace ProbabilityTheory

/-- A finite product of Gaussian measures is Gaussian. The characteristic function of the
product is the product of the factors' characteristic functions, and the mean and variance
of a linear form split over its restrictions to the factors. -/
instance isGaussian_pi {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, IsGaussian (μ i)] : IsGaussian (Measure.pi μ) := by
  classical
  refine isGaussian_of_charFunDual_eq fun L ↦ ?_
  -- A linear form on the product is the sum of its restrictions to the factors.
  have hL : ⇑L = ∑ i, fun x : (i : ι) → E i ↦ L.comp (.single ℝ E i) (x i) := by
    funext x
    simpa only [Finset.sum_apply] using
      (ContinuousLinearMap.sum_comp_single (L := L) (v := x)).symm
  have hmean : (Measure.pi μ)[L] = ∑ i, (μ i)[L.comp (.single ℝ E i)] := by
    simp only [hL, Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ ↦ integrable_comp_eval (IsGaussian.integrable_dual _ _)]
    exact Finset.sum_congr rfl fun i _ ↦ integral_comp_eval (by fun_prop)
  have hvar : Var[L; Measure.pi μ] = ∑ i, Var[L.comp (.single ℝ E i); μ i] := by
    rw [hL]
    exact variance_sum_pi fun i ↦ IsGaussian.memLp_dual (μ i) _ 2 (by simp)
  rw [charFunDual_pi, integral_complex_ofReal, hmean, hvar]
  simp_rw [IsGaussian.charFunDual_eq, ← Complex.exp_sum, integral_complex_ofReal]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div]

end ProbabilityTheory

namespace TauCeti.Probability

variable (ι : Type*) [Fintype ι]

/-- The joint standard Gaussian density on `ℝ^ι` is everywhere positive. -/
theorem prod_gaussianPDFReal_pos (x : ι → ℝ) : 0 < ∏ i, gaussianPDFReal 0 1 (x i) :=
  Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 1 (x i) one_ne_zero

/-- **The joint standard Gaussian density on `ℝ^ι` in closed form**: the normalisation
`(2π)^(-d/2)` in the dimension `d`, times the exponential of minus half the sum of the squared
coordinates. -/
theorem prod_gaussianPDFReal_zero_one (x : ι → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (x i)
      = (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) * exp (-(∑ i, x i ^ 2) / 2) := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hconst : (√(2 * π))⁻¹ ^ Fintype.card ι = (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) :=
    Real.inv_sqrt_pow_eq_rpow hπ.le _
  have hexp : ∑ i, -(x i ^ 2 / 2) = -(∑ i, x i ^ 2) / 2 := by
    rw [Finset.sum_neg_distrib, ← Finset.sum_div]
    ring
  rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => gaussianPDFReal_zero_one (x i),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, hconst, hexp]

/-- The joint standard Gaussian density on `ℝ^ι` is measurable. -/
theorem measurable_prod_gaussianPDFReal :
    Measurable fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 1 (x i) :=
  Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

/-- **The standard Gaussian on `ℝ^ι` is `volume^ι` weighted by the joint density.** Each factor is
`volume` weighted by `gaussianPDFReal 0 1` (`ProbabilityTheory.gaussianReal_of_var_ne_zero`), and
coordinatewise densities multiply (`TauCeti.pi_withDensity`). -/
theorem pi_gaussianReal_eq_withDensity :
    (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))
      = (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
        fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i)) := by
  have hγ : (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))
      = (gaussianReal 0 1 : Measure ℝ) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianPDF_def]
  have : IsProbabilityMeasure
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
    rw [hγ]; infer_instance
  have hfam : (fun _ : ι => (gaussianReal 0 1 : Measure ℝ))
      = fun _ : ι => volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x) :=
    funext fun _ => hγ.symm
  rw [hfam, pi_withDensity (fun _ : ι => (volume : Measure ℝ)) fun _ =>
      (measurable_gaussianPDFReal 0 1).ennreal_ofReal]
  exact withDensity_congr_ae (Filter.Eventually.of_forall fun x =>
    (ENNReal.ofReal_prod_of_nonneg fun i _ =>
      (gaussianPDFReal_pos 0 1 (x i) one_ne_zero).le).symm)

/-- **`volume^ι` is absolutely continuous with respect to `γ^ι`.** The joint density is everywhere
positive, so weighting by it kills no set of positive measure. This is what moves an
almost-everywhere identification of a `L²(γ^ι)` representative to one holding `volume^ι`-almost
everywhere, where the `√`-density envelope lives. -/
theorem pi_volume_absolutelyContinuous_pi_gaussianReal :
    (Measure.pi fun _ : ι => (volume : Measure ℝ))
      ≪ Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ) := by
  rw [pi_gaussianReal_eq_withDensity]
  exact absolutelyContinuous_withDensity_ofReal (measurable_prod_gaussianPDFReal ι).aemeasurable
    (.of_forall (prod_gaussianPDFReal_pos ι))

end TauCeti.Probability
