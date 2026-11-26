/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.VariationMeasure
public import TauCeti.Analysis.BoundedVariation.Hyperplane
public import TauCeti.Probability.Distributions.Gaussian.Density
public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Geometry.Euclidean.Volume.Measure
public import TauCeti.Probability.Distributions.Gaussian.IsoperimetricProfile
public import TauCeti.Probability.Distributions.Gaussian.OrthogonalSplitting
import Mathlib.MeasureTheory.Integral.Layercake
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The weighted perimeter of a half-space

For a `C¹` weight `W`, a unit vector `ν` and `c ∈ ℝ`, the weighted perimeter of the half-space
`H = {x | ⟪x, ν⟫ < c}` in an open set `Ω` is the integral of the density `e^{−W}` against the
`(n − 1)`-dimensional Hausdorff measure on the part of the boundary hyperplane in `Ω`
(`TauCeti.weightedPerimeter_setOf_inner_lt`). For the Gaussian weight this gives
`P_γ({x | ⟪x, ν⟫ < c}) = φ(c)`, the standard normal density at `c`
(`TauCeti.gaussianPerimeter_setOf_inner_lt`), and likewise `P_γ({x | c < ⟪x, ν⟫}) = φ(c)`
(`TauCeti.gaussianPerimeter_setOf_lt_inner`). Rescaling a nonzero `ν` to unit length, a
half-space of Gaussian measure `v` has Gaussian perimeter `I(v)`, the Gaussian isoperimetric
function (`TauCeti.gaussianPerimeter_setOf_inner_lt_eq_gaussianIsoperimetricProfile`).

The route: `V_μ(1_H; Ω) = ∫ e^{−W} d|D1_H|`
(`TauCeti.weightedVariation_eq_lintegral_variationMeasure`) and the layer-cake formula write
both sides as `∫₀^∞` of the masses of the open superlevel sets `{e^{−W} > t}`.
On an open set `U` the perimeter measure of `H` is the Euclidean perimeter
`P(H; U) = Hⁿ⁻¹(U ∩ {⟪x, ν⟫ = c})` (`TauCeti.perimeter_setOf_inner_lt`). For the Gaussian weight,
the hyperplane is parametrised by `y ↦ c ν + y` on `ν^⊥`
(`TauCeti.euclideanHausdorffMeasure_restrict_setOf_inner_eq`), and the Gaussian density at
`c ν + y` is `φ(c)` times the Gaussian density of `ν^⊥` at `y`, which integrates to `1`.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Module Metric ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {ν : E}

/-- **The weighted perimeter of a half-space.** For a `C¹` weight `W`, a unit vector `ν` and an
open set `Ω`, `P_μ({x | ⟪x, ν⟫ < c}; Ω) = ∫_{Ω ∩ {⟪x, ν⟫ = c}} e^{−W} dHⁿ⁻¹`. -/
theorem weightedPerimeter_setOf_inner_lt (hW : ContDiff ℝ 1 W) (hν : ‖ν‖ = 1) (c : ℝ)
    (Ω : Opens E) :
    weightedPerimeter W Ω {x | ⟪x, ν⟫ < c} =
      ∫⁻ x in (Ω : Set E) ∩ {x | ⟪x, ν⟫ = c}, ENNReal.ofReal (Real.exp (-W x))
        ∂μHE[finrank ℝ E - 1] := by
  set H := {x : E | ⟪x, ν⟫ < c}
  have hH : MeasurableSet H := measurableSet_lt (by fun_prop) measurable_const
  have hu : LocallyIntegrableOn (H.indicator (1 : E → ℝ)) Ω :=
    locallyIntegrableOn_indicator_const hH.nullMeasurableSet 1
  have hfin (K : Set E) (hK : IsCompact K) (_ : K ⊆ Ω) :=
    exists_totalVariationOn_indicator_setOf_inner_lt_ne_top hν c hK
  have hρ : Continuous fun x : E => Real.exp (-W x) := Real.continuous_exp.comp hW.continuous.neg
  rw [weightedPerimeter_def, weightedVariation_eq_lintegral_variationMeasure hW hu hfin,
    lintegral_eq_lintegral_meas_lt _ (.of_forall fun _ => (Real.exp_pos _).le)
      (hρ.comp continuous_subtypeVal).measurable.aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (.of_forall fun _ => (Real.exp_pos _).le)
      hρ.measurable.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  -- Both sides are the masses of the open superlevel set `U = {e^{−W} > t} ∩ Ω`.
  let U : Opens E := ⟨{y | t < Real.exp (-W y)} ∩ Ω,
    (isOpen_lt continuous_const hρ).inter Ω.isOpen⟩
  have hpre : {x : Ω | t < Real.exp (-W x)} = (↑) ⁻¹' (U : Set E) := by
    ext x
    simp [U]
  rw [hpre, variationMeasure_preimage_coe hu hfin (show U ≤ Ω from fun _ hx => hx.2),
    ← perimeter_def,
    perimeter_setOf_inner_lt hν c U,
    Measure.restrict_apply (isOpen_lt continuous_const hρ).measurableSet]
  congr 1
  ext x
  simp only [U, Opens.coe_mk, mem_inter_iff, mem_ofPred_eq]
  tauto

/-- **The Gaussian perimeter of a half-space.** For a unit vector `ν`, the half-space
`{x | ⟪x, ν⟫ < c}` has Gaussian perimeter `φ(c)`, the standard normal density at `c`. -/
theorem gaussianPerimeter_setOf_inner_lt (hν : ‖ν‖ = 1) (c : ℝ) :
    gaussianPerimeter {x : E | ⟪x, ν⟫ < c} = ENNReal.ofReal (gaussianPDFReal 0 1 c) := by
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (hν ▸ one_ne_zero)
  have : Nontrivial E := ⟨⟨ν, 0, hν0⟩⟩
  have hn : (finrank ℝ (ℝ ∙ ν)ᗮ : ℝ) = finrank ℝ E - 1 := by
    have : Fact (finrank ℝ E = finrank ℝ E - 1 + 1) :=
      ⟨(Nat.sub_add_cancel finrank_pos).symm⟩
    rw [Submodule.finrank_orthogonal_span_singleton (n := finrank ℝ E - 1) hν0,
      Nat.cast_sub (finrank_pos (R := ℝ) (M := E)), Nat.cast_one]
  set ρ : (ℝ ∙ ν)ᗮ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(finrank ℝ (ℝ ∙ ν)ᗮ : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / 2))
  have hρ : Measurable ρ := by fun_prop
  -- The Gaussian density at `c ν + y` is `φ(c)` times the Gaussian density of `ν^⊥` at `y`.
  have hsplit (y : (ℝ ∙ ν)ᗮ) : ENNReal.ofReal (Real.exp (-gaussianWeight E (c • ν + (y : E)))) =
      ENNReal.ofReal (gaussianPDFReal 0 1 c) * ρ y := by
    have hy : ⟪ν, (y : E)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self ν) y.property
    have hnorm : ‖c • ν + (y : E)‖ ^ 2 = c ^ 2 + ‖y‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_left, hy, norm_smul, hν, Real.norm_eq_abs,
        Submodule.norm_coe]
      simp [sq_abs]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 c)]
    congr 1
    rw [gaussianWeight_def, hnorm, hn, Real.rpow_def_of_pos (by positivity)]
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity), ← Real.exp_neg, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hmap : Measurable fun y : (ℝ ∙ ν)ᗮ => c • ν + (y : E) := by fun_prop
  have hg : Measurable fun x : E => ENNReal.ofReal (Real.exp (-gaussianWeight E x)) :=
    continuous_exp_neg_gaussianWeight.measurable.ennreal_ofReal
  rw [gaussianPerimeter_def, weightedPerimeter_setOf_inner_lt contDiff_gaussianWeight hν c ⊤,
    Opens.coe_top, univ_inter, euclideanHausdorffMeasure_restrict_setOf_inner_eq hν c,
    lintegral_map hg hmap]
  simp_rw [hsplit]
  rw [lintegral_const_mul _ hρ, ← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← Probability.stdGaussian_eq_withDensity_norm, measure_univ, mul_one]

/-- For a nonzero vector `ν`, the half-space `{x | ⟪x, ν⟫ < c}` has Gaussian perimeter
`φ(c / ‖ν‖)`. -/
theorem gaussianPerimeter_setOf_inner_lt_of_ne_zero (hν : ν ≠ 0) (c : ℝ) :
    gaussianPerimeter {x : E | ⟪x, ν⟫ < c} = ENNReal.ofReal (gaussianPDFReal 0 1 (c / ‖ν‖)) := by
  rw [setOf_inner_lt_eq_smul_inv_norm hν,
    gaussianPerimeter_setOf_inner_lt (ν := ‖ν‖⁻¹ • ν) (norm_smul_inv_norm hν)]

/-- **A half-space of Gaussian measure `v` has Gaussian perimeter `I(v)`.** This holds for every
vector `ν`: for `ν = 0` the set is `∅` or `E`, of perimeter `0 = I(0) = I(1)`. -/
theorem gaussianPerimeter_setOf_inner_lt_eq_gaussianIsoperimetricProfile (ν : E) (c : ℝ) :
    gaussianPerimeter {x : E | ⟪x, ν⟫ < c} = ENNReal.ofReal
      (Probability.gaussianIsoperimetricProfile ((stdGaussian E).real {x | ⟪x, ν⟫ < c})) := by
  rcases eq_or_ne ν 0 with rfl | hν
  · by_cases hc : 0 < c
    · simp [hc, gaussianPerimeter_univ, Probability.gaussianIsoperimetricProfile_one]
    · simp [hc, gaussianPerimeter_empty, Probability.gaussianIsoperimetricProfile_zero]
  rw [gaussianPerimeter_setOf_inner_lt_of_ne_zero hν, setOf_inner_lt_eq_smul_inv_norm hν,
    Probability.measureReal_stdGaussian_setOf_inner_lt (ν := ‖ν‖⁻¹ • ν) (norm_smul_inv_norm hν),
    Probability.gaussianIsoperimetricProfile_cdf]

/-- **The Gaussian perimeter of an upper half-space.** For a unit vector `ν`, the half-space
`{x | c < ⟪x, ν⟫}` has Gaussian perimeter `φ(c)`, the standard normal density at `c`. -/
theorem gaussianPerimeter_setOf_lt_inner (hν : ‖ν‖ = 1) (c : ℝ) :
    gaussianPerimeter {x : E | c < ⟪x, ν⟫} = ENNReal.ofReal (gaussianPDFReal 0 1 c) := by
  have h : {x : E | c < ⟪x, ν⟫} = {x | ⟪x, -ν⟫ < -c} := by
    ext x
    simp [inner_neg_right]
  rw [h, gaussianPerimeter_setOf_inner_lt (by rwa [norm_neg]) (-c)]
  simp [gaussianPDFReal_def]

end TauCeti
