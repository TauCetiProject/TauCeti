/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation scaling of the `Lᵖ` seminorm

Dilating the variable of a function on a finite-dimensional real normed space `E` by `r⁻¹`, for
`r > 0`, multiplies its `Lᵖ` seminorm against an additive Haar measure by `r ^ (n / p)`, where
`n` is the dimension of `E`. Here `n / p` stands for `n / p.toReal`, which is `0` at `p = 0` and
`p = ∞` by Lean's conventions `ENNReal.toReal ∞ = 0` and `x / 0 = 0`, so at those two exponents
the factor is `1`. This is the `eLpNorm` counterpart of the lower Lebesgue integral law
`TauCeti.lintegral_comp_inv_smul`.

More generally, composing with a linear automorphism `e` multiplies the `Lᵖ` seminorm by
`|det e|^(-1 / p)`, and the `Lᵖ` seminorm on a preimage `e ⁻¹' s` by the same factor relative to
the `Lᵖ` seminorm on `s`.

## Main declarations

* `TauCeti.eLpNorm_comp_inv_smul`: `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`.
* `TauCeti.eLpNorm_comp_continuousLinearEquiv`: `‖u ∘ e‖_p = |det e|^(-1 / p) * ‖u‖_p`.
* `TauCeti.eLpNorm_comp_continuousLinearEquiv_restrict_preimage`: the same identity for the `Lᵖ`
  seminorms on `e ⁻¹' s` and on `s`.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {G : Type*} [TopologicalSpace G] [ContinuousENorm G]

/-- **Dilation scaling of the `Lᵖ` seminorm:** `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`, where
`n` is the dimension of the ambient space. The exponent `n / p` is `n / p.toReal`, which is `0` at
`p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem eLpNorm_comp_inv_smul (u : E → G) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) :
    eLpNorm (fun x => u (r⁻¹ • x)) p μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal)) * eLpNorm u p μ := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  rw [← Function.comp_def, ← (measurableEmbedding_const_smul₀ hr').eLpNorm_map_measure,
    Measure.map_addHaar_smul μ hr', eLpNorm_smul_measure_of_ne_zero (by positivity), smul_eq_mul]
  congr 1
  rw [inv_pow, inv_inv, abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul hr.le, one_div, ENNReal.toReal_inv, div_eq_mul_inv]

/-- **Linear change of variables in the `Lᵖ` seminorm:** composing with a linear automorphism `e`
multiplies the `Lᵖ` seminorm against an additive Haar measure by `|det e|^(-1 / p)`. The exponent
`1 / p` is `(1 / p).toReal`, which is `0` at `p = 0` and `p = ∞`, where the factor is thus `1`. -/
theorem eLpNorm_comp_continuousLinearEquiv (u : E → G) (e : E ≃L[ℝ] E) (p : ℝ≥0∞) :
    eLpNorm (u ∘ e) p μ = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
      eLpNorm u p μ := by
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hmap : Measure.map e μ = ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| • μ :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  rw [← he.eLpNorm_map_measure, hmap, eLpNorm_smul_measure_of_ne_zero (by simpa using hdet),
    smul_eq_mul]

/-- **Linear change of variables in the `Lᵖ` seminorm on a set:** composing with a linear
automorphism `e` multiplies the `Lᵖ` seminorm on `e ⁻¹' s`, against an additive Haar measure, by
`|det e|^(-1 / p)` relative to the `Lᵖ` seminorm of the function on `s`. -/
theorem eLpNorm_comp_continuousLinearEquiv_restrict_preimage {F : Type*} [NormedAddCommGroup F]
    (u : E → F) (e : E ≃L[ℝ] E) (p : ℝ≥0∞) {s : Set E} (hs : MeasurableSet s) :
    eLpNorm (u ∘ e) p (μ.restrict (e ⁻¹' s)) =
      ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
        eLpNorm u p (μ.restrict s) := by
  have hind : (e ⁻¹' s).indicator (u ∘ e) = s.indicator u ∘ e :=
    funext fun _ => Set.indicator_comp_right e
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict
      (hs.preimage e.continuous.measurable).nullMeasurableSet, hind,
    eLpNorm_comp_continuousLinearEquiv, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]

end TauCeti
