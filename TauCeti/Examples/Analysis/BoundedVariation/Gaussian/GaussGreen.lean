/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.HalfSpace
public import TauCeti.Analysis.BoundedVariation.Weighted.Translation
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import TauCeti.Probability.Distributions.Gaussian.OrthogonalSplitting
import TauCeti.Analysis.InnerProductSpace.HalfSpace

/-!
# Checks: the weighted Gauss–Green formula for the Gaussian weight

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2`, with standard
Gaussian measure `γ`, Gaussian weight `W` (so `γ = e^{−W} · volume`), `φ = gaussianPDFReal 0 1`
and `Φ = cdf (gaussianReal 0 1)`.

* **Half-spaces.** For a unit vector `ν` and `U = {x | ⟪x, ν⟫ < s}`, the translate `U + t ν` is
  `{x | ⟪x, ν⟫ < s + t}`, so `γ(U + t ν) = Φ(s + t)`, whose derivative at `t = 0` is `φ(s)`.
  By the translation formula `TauCeti.hasDerivAt_measureReal_stdGaussian_smul_vadd`, the flux
  `∫_{∂*U} ⟨ν, ν_U⟩ e^{−W} dHⁿ⁻¹` of `ν` through the reduced boundary is therefore `φ(s)`; it is
  positive, so the normal `ν_U` of the formula points out of `U` (an inner normal would give
  `−φ(s)`).
* **The whole space.** `E` has empty reduced boundary (its perimeter in every ball is zero). For
  the bounded constant field `w`, whose Gaussian divergence is `−⟨x, w⟩`, the bounded-field
  formula `TauCeti.integral_weightedDivergence_eq_integral_reducedBoundary_of_bounded` therefore
  gives `∫ ⟨x, w⟩ dγ = 0`, matching the vanishing mean of `γ`
  (`ProbabilityTheory.integral_strongDual_stdGaussian`).

The formulas need dimension `n ≥ 2`, so the case of the line is not covered here.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Module TauCeti TauCeti.Probability TauCeti.MeasureTheory
open scoped ENNReal RealInnerProductSpace Pointwise

namespace TauCeti.Examples.GaussianGaussGreen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian measure of the translated half-space is `Φ(s + t)`. -/
theorem measureReal_stdGaussian_smul_vadd_setOf_inner_lt {ν : E} (hν : ‖ν‖ = 1) (s t : ℝ) :
    (stdGaussian E).real ((t • ν) +ᵥ {x : E | ⟪x, ν⟫ < s}) = cdf (gaussianReal 0 1) (s + t) := by
  simp [vadd_setOf_inner_lt, real_inner_smul_left, hν, measureReal_stdGaussian_setOf_inner_lt hν]

/-- For a unit vector `ν`, `t ↦ γ((t • ν) +ᵥ {x | ⟪x, ν⟫ < s})` has derivative `φ(s)` at `0`. -/
theorem hasDerivAt_measureReal_stdGaussian_smul_vadd_setOf_inner_lt {ν : E} (hν : ‖ν‖ = 1)
    (s : ℝ) :
    HasDerivAt (fun t : ℝ => (stdGaussian E).real ((t • ν) +ᵥ {x : E | ⟪x, ν⟫ < s}))
      (gaussianPDFReal 0 1 s) 0 := by
  simp_rw [measureReal_stdGaussian_smul_vadd_setOf_inner_lt hν]
  simpa using (hasDerivAt_cdf_gaussianReal 0 one_ne_zero (s + 0)).comp_const_add s 0

/-- **The flux through a half-space.** For `n ≥ 2` and a unit vector `ν`, the Gaussian-weighted
flux of `ν` through the reduced boundary of `{x | ⟪x, ν⟫ < s}` is `φ(s)`. -/
theorem integral_reducedBoundary_setOf_inner_lt (hn : 2 ≤ finrank ℝ E) {ν : E} (hν : ‖ν‖ = 1)
    (s : ℝ) :
    ∫ x in reducedBoundary volume ⊤ {x : E | ⟪x, ν⟫ < s},
        ⟪ν, outerNormal volume ⊤ {x : E | ⟪x, ν⟫ < s} x⟫ * Real.exp (-gaussianWeight E x)
          ∂μHE[finrank ℝ E - 1] = gaussianPDFReal 0 1 s := by
  have hs : NullMeasurableSet {x : E | ⟪x, ν⟫ < s} :=
    (measurableSet_lt (by fun_prop) measurable_const).nullMeasurableSet
  have hP : gaussianPerimeter {x : E | ⟪x, ν⟫ < s} ≠ ∞ := by
    rw [gaussianPerimeter_setOf_inner_lt hν]
    exact ENNReal.ofReal_ne_top
  exact (hasDerivAt_measureReal_stdGaussian_smul_vadd hn hs hP ν).unique
    (hasDerivAt_measureReal_stdGaussian_smul_vadd_setOf_inner_lt hν s)

/-- The flux of the outer normal direction through a half-space is positive; an inner normal
would make it `−φ(s) < 0`. -/
example (hn : 2 ≤ finrank ℝ E) {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) :
    0 < ∫ x in reducedBoundary volume ⊤ {x : E | ⟪x, ν⟫ < s},
        ⟪ν, outerNormal volume ⊤ {x : E | ⟪x, ν⟫ < s} x⟫ * Real.exp (-gaussianWeight E x)
          ∂μHE[finrank ℝ E - 1] := by
  rw [integral_reducedBoundary_setOf_inner_lt hn hν]
  exact gaussianPDFReal_pos 0 1 s one_ne_zero

/-- **The whole space.** For `n ≥ 2` and every `w`, `∫ ⟨x, w⟩ e^{−W(x)} dx = 0`: the
Gauss–Green formula on `U = E` for the constant field `w`, whose Gaussian divergence is
`−⟨x, w⟩`. -/
theorem integral_inner_mul_exp_neg_gaussianWeight (hn : 2 ≤ finrank ℝ E) (w : E) :
    ∫ x, ⟪x, w⟫ * Real.exp (-gaussianWeight E x) = 0 := by
  have hWX : Integrable fun x : E =>
      fderiv ℝ (gaussianWeight E) x w * Real.exp (-gaussianWeight E x) := by
    simpa [fderiv_gaussianWeight] using integrable_inner_mul_exp_neg_gaussianWeight w
  have hP : weightedPerimeter (gaussianWeight E) ⊤ (univ : Set E) ≠ ∞ := by
    rw [← gaussianPerimeter_def, gaussianPerimeter_univ]
    exact ENNReal.zero_ne_top
  have key := integral_weightedDivergence_eq_integral_reducedBoundary_of_bounded
    (W := gaussianWeight E) (X := fun _ => w) contDiff_gaussianWeight hn
    integrable_exp_neg_gaussianWeight nullMeasurableSet_univ hP contDiff_const (C := ‖w‖)
    (C' := 0) (fun _ => le_rfl) (fun x => by simp) hWX
  -- the whole space has empty reduced boundary, so the boundary integral vanishes
  rw [reducedBoundary_univ, Measure.restrict_empty, integral_zero_measure] at key
  simpa [fderiv_gaussianWeight, integral_neg] using key

/-- The same vanishing, read as the vanishing mean of the standard Gaussian measure. -/
example (w : E) : ∫ x, ⟪x, w⟫ ∂(stdGaussian E) = 0 := by
  simpa [real_inner_comm] using integral_strongDual_stdGaussian (innerSL ℝ w)

end TauCeti.Examples.GaussianGaussGreen
