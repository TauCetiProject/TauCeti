/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convolution.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Convolution of real densities

Mathlib describes convolution densities using the lower Lebesgue integral of
`ℝ≥0∞`-valued functions.  For nonnegative real functions whose Bochner convolution exists,
this file identifies that density with the `ENNReal.ofReal` lift of the ordinary real
convolution.  It then packages the corresponding convolution identity for measures presented
by real densities.

These bridges allow pointwise analytic properties of the ordinary convolution, such as
continuity and strict positivity, to be combined with measure-level convolution identities.

## Main results

* `MeasureTheory.lconvolution_ofReal_eq_ofReal_convolution` identifies the lower-integral and
  Bochner convolutions of nonnegative real functions.
* `MeasureTheory.conv_withDensity_ofReal_eq_withDensity_convolution` computes the convolution of
  two measures presented by nonnegative real densities.
* `MeasureTheory.continuous_eq_of_withDensity_ofReal_eq` identifies continuous nonnegative real
  densities pointwise from equality of their weighted measures.
-/

public section

open Function Set ContinuousLinearMap
open scoped Convolution ENNReal MeasureTheory

namespace MeasureTheory

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] {μ : Measure G} {f g : G → ℝ}

private theorem lconvolution_ofReal_apply_eq_ofReal_convolution (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (x : G) (hfg : ConvolutionExistsAt f g x (mul ℝ ℝ) μ) :
    ((fun y ↦ ENNReal.ofReal (f y)) ⋆ₗ[μ] (fun y ↦ ENNReal.ofReal (g y))) x =
      ENNReal.ofReal ((f ⋆[mul ℝ ℝ, μ] g) x) := by
  rw [lconvolution_def, convolution_def,
    ofReal_integral_eq_lintegral_ofReal hfg.integrable
      (.of_forall fun y ↦ mul_nonneg (hf0 y) (hg0 (x - y)))]
  refine lintegral_congr fun y ↦ ?_
  rw [← ENNReal.ofReal_mul (hf0 y)]
  simp only [mul_apply', sub_eq_add_neg, add_comm x]

/-- The lower-integral convolution of the `ENNReal.ofReal` lifts of two nonnegative real
functions is the lift of their Bochner convolution, provided the latter exists everywhere. -/
theorem lconvolution_ofReal_eq_ofReal_convolution (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfg : ConvolutionExists f g (mul ℝ ℝ) μ) :
    (fun x ↦ ENNReal.ofReal (f x)) ⋆ₗ[μ] (fun x ↦ ENNReal.ofReal (g x)) =
      fun x ↦ ENNReal.ofReal ((f ⋆[mul ℝ ℝ, μ] g) x) := by
  funext x
  exact lconvolution_ofReal_apply_eq_ofReal_convolution hf0 hg0 x (hfg x)

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [μ.IsAddLeftInvariant]

/-- Convolving two measures with nonnegative real densities produces the measure whose real
density is their Bochner convolution, provided the latter exists almost everywhere. -/
theorem conv_withDensity_ofReal_eq_withDensity_convolution (hf : Measurable f)
    (hg : Measurable g) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfg : ∀ᵐ x ∂μ, ConvolutionExistsAt f g x (mul ℝ ℝ) μ) :
    μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∗
        μ.withDensity (fun x ↦ ENNReal.ofReal (g x)) =
      μ.withDensity (fun x ↦ ENNReal.ofReal ((f ⋆[mul ℝ ℝ, μ] g) x)) := by
  rw [conv_withDensity_eq_lconvolution hf.ennreal_ofReal hg.ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [hfg] with x hx
  exact lconvolution_ofReal_apply_eq_ofReal_convolution hf0 hg0 x hx

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {ν : Measure X} [SigmaFinite ν] [ν.IsOpenPosMeasure] {p q : X → ℝ}

/-- Continuous nonnegative real densities that present the same measure are equal pointwise. -/
theorem continuous_eq_of_withDensity_ofReal_eq (hp : Continuous p) (hq : Continuous q)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (h : ν.withDensity (fun x ↦ ENNReal.ofReal (p x)) =
      ν.withDensity (fun x ↦ ENNReal.ofReal (q x))) :
    p = q := by
  have haeENN : (fun x ↦ ENNReal.ofReal (p x)) =ᵐ[ν] fun x ↦ ENNReal.ofReal (q x) :=
    (withDensity_eq_iff_of_sigmaFinite hp.measurable.ennreal_ofReal.aemeasurable
      hq.measurable.ennreal_ofReal.aemeasurable).1 h
  have hae : p =ᵐ[ν] q := by
    filter_upwards [haeENN] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hp0 x) (hq0 x)).mp hx
  exact (hp.ae_eq_iff_eq ν hq).1 hae

end MeasureTheory
