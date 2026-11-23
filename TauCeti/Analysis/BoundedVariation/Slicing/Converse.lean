/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
import TauCeti.Analysis.BoundedVariation.Slicing.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# The converse slicing inequality for functions of bounded variation

Let `E` be a finite-dimensional real inner product space with its volume, `Ω ⊆ E` open, and
`e` a unit vector. For `y` in the orthogonal hyperplane `(ℝ ∙ e)ᗮ`, the line through `y` in
direction `e` meets `Ω` in the open set of parameters `{t | y + t • e ∈ Ω}`. For a function `u`
locally integrable on `Ω`, the one-dimensional variations of its restrictions
`t ↦ u (y + t • e)` to these open sets control the variation of `u` along `e`: for a scalar test
function `ψ` on `Ω` with `|ψ| ≤ 1`,

`∫_Ω ∂_e ψ · u ≤ ∫_{(ℝ ∙ e)ᗮ} |D(u (y + · • e))|({t | y + t • e ∈ Ω}) dy`

(`TauCeti.ofReal_integral_lineDerivOp_mul_le_lintegral_totalVariationOn_line`). Expanding the
divergence of a test vector field in an orthonormal basis `b` and applying this in each direction
`b i` gives

`|Du|(Ω) ≤ ∑ i, ∫_{(ℝ ∙ b i)ᗮ} |D(u (y + · • b i))|({t | y + t • b i ∈ Ω}) dy`

(`TauCeti.totalVariationOn_le_sum_lintegral_totalVariationOn_line`), and for a set `s`

`P(s; Ω) ≤ ∑ i, ∫_{(ℝ ∙ b i)ᗮ} P({t | y + t • b i ∈ s}; {t | y + t • b i ∈ Ω}) dy`

(`TauCeti.perimeter_le_sum_lintegral_perimeter_lineSection`). These are extended-valued
inequalities with no finiteness hypothesis. In particular, if the perimeters of the line sections
of `s` in the coordinate directions have finite integrals, then `s` has finite perimeter in `Ω`
(`TauCeti.perimeter_lt_top_of_lintegral_perimeter_lineSection_lt_top`). This is the converse of
the slicing inequality `TauCeti.lintegral_perimeter_lineSection_le`, and is the step of the
proof of Federer's criterion for finite perimeter that passes from line sections to the
ambient set.

The proof restricts the test function `ψ` to each line, giving a test function on the open set
of parameters whose derivative is `∂_e ψ` along the line, and splits the integral over `Ω` along
the lines by Fubini's theorem in orthogonal line coordinates.

## Main results

* `TauCeti.ofReal_integral_lineDerivOp_mul_le_lintegral_totalVariationOn_line`: the pairing of
  `u` with the derivative `∂_e ψ` of a test function is controlled by the variations on lines.
* `TauCeti.totalVariationOn_le_sum_lintegral_totalVariationOn_line`: the total variation on `Ω`
  is at most the sum over an orthonormal basis of the integrated variations on lines.
* `TauCeti.perimeter_le_sum_lintegral_perimeter_lineSection` and
  `TauCeti.perimeter_lt_top_of_lintegral_perimeter_lineSection_lt_top`: the same for the
  perimeter of a set and the perimeters of its line sections.

## References

* H. Federer, *Geometric Measure Theory*, 4.5.11 (the criterion for finite perimeter by
  slicing).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.11 (slicing of functions of bounded variation).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.11 (the
  criterion for finite perimeter).
-/

public section

open MeasureTheory Set TopologicalSpace TestFunction LineDeriv
open scoped ENNReal Distributions RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

namespace TauCeti

omit [MeasurableSpace E] [BorelSpace E] in
/-- The restriction `t ↦ ψ (y + t • e)` of a scalar test function on `Ω` to the line through `y`
in a nonzero direction `e`, as a test function on the open set of parameters of the line lying
in `Ω`. -/
private noncomputable def lineTestFunction (ψ : 𝓓(Ω, ℝ)) (y e : E) (he : e ≠ 0) :
    𝓓(Opens.comap ⟨fun t : ℝ => y + t • e, by fun_prop⟩ Ω, ℝ) :=
  ⟨fun t => ψ (y + t • e), ψ.contDiff.comp (contDiff_const.add (contDiff_id.smul contDiff_const)),
    ψ.hasCompactSupport.comp_isClosedEmbedding
      ((Homeomorph.addLeft y).isClosedEmbedding.comp (isClosedEmbedding_smul_left he)),
    (tsupport_comp_subset_preimage (ψ : E → ℝ) (by fun_prop : Continuous fun t : ℝ => y + t • e))
      |>.trans fun _ ht => ψ.tsupport_subset ht⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem lineTestFunction_apply (ψ : 𝓓(Ω, ℝ)) (y e : E) (he : e ≠ 0) (t : ℝ) :
    lineTestFunction ψ y e he t = ψ (y + t • e) :=
  (rfl)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The divergence of the restriction of `ψ` to a line is the derivative `∂_e ψ` along it. -/
private theorem divergenceCLM_lineTestFunction (ψ : 𝓓(Ω, ℝ)) (y e : E) (he : e ≠ 0) (t : ℝ) :
    divergenceCLM (lineTestFunction ψ y e he) t = ∂_{e} ψ (y + t • e) := by
  rw [divergenceCLM_apply_eq_deriv, lineDerivOp_apply_eq_fderiv]
  have hl : HasDerivAt (fun s : ℝ => y + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add y
  exact ((ψ.contDiff.differentiable (by simp) (y + t • e)).hasFDerivAt.comp_hasDerivAt t hl).deriv

/-- **Variation along a direction is controlled by the variations on lines.** Let `u` be locally
integrable on `Ω`, `e` a unit vector and `ψ` a scalar test function on `Ω` with `|ψ| ≤ 1`. Then
the pairing of `u` with the derivative `∂_e ψ` is at most the integral, over the orthogonal
hyperplane `(ℝ ∙ e)ᗮ`, of the variations of the restrictions `t ↦ u (y + t • e)` on the open
sets `{t | y + t • e ∈ Ω}`. -/
theorem ofReal_integral_lineDerivOp_mul_le_lintegral_totalVariationOn_line {u : E → ℝ}
    (hu : LocallyIntegrableOn u Ω) (e : E) (he : ‖e‖ = 1) (ψ : 𝓓(Ω, ℝ))
    (hψ : ∀ x, ‖ψ x‖ ≤ 1) :
    ENNReal.ofReal (∫ x, ∂_{e} ψ x * u x) ≤
      ∫⁻ y : (ℝ ∙ e)ᗮ, totalVariationOn volume
        (Opens.comap ⟨fun t : ℝ => (y : E) + t • e, by fun_prop⟩ Ω)
        (fun t : ℝ => u ((y : E) + t • e)) := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hL := measurePreserving_orthogonalLineEquiv e he
  have hLe := (orthogonalLineEquiv e he).toHomeomorph.measurableEmbedding
  have hg : Integrable (fun x => ∂_{e} ψ x * u x) := by
    simpa using TestFunction.integrable_smul (∂_{e} ψ) hu
  -- Fubini's theorem in orthogonal line coordinates.
  have hsplit : ∫ x, ∂_{e} ψ x * u x = ∫ y : (ℝ ∙ e)ᗮ, ∫ t : ℝ,
      divergenceCLM (lineTestFunction ψ (y : E) e he0) t * u ((y : E) + t • e) := by
    rw [← hL.integral_comp hLe]
    have := integral_prod _ (hL.integrable_comp_of_integrable hg)
    simp only [Function.comp_def] at this
    rw [this]
    simp only [orthogonalLineEquiv_apply, divergenceCLM_lineTestFunction]
  rw [hsplit]
  refine MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans (lintegral_mono fun y => ?_)
  refine ofReal_integral_le_totalVariationOn _ fun t => ?_
  rw [lineTestFunction_apply]
  exact hψ _

/-- **The converse slicing inequality.** For `u` locally integrable on `Ω` and an orthonormal
basis `b` of `E`, the total variation of `u` on `Ω` is at most the sum over `i` of the integrals,
over the hyperplanes `(ℝ ∙ b i)ᗮ`, of the variations of the restrictions `t ↦ u (y + t • b i)` on
the open sets `{t | y + t • b i ∈ Ω}`:

`|Du|(Ω) ≤ ∑ i, ∫_{(ℝ ∙ b i)ᗮ} |D(u (y + · • b i))|({t | y + t • b i ∈ Ω}) dy`. -/
theorem totalVariationOn_le_sum_lintegral_totalVariationOn_line {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {u : E → ℝ} (hu : LocallyIntegrableOn u Ω) :
    totalVariationOn volume Ω u ≤ ∑ i, ∫⁻ y : (ℝ ∙ b i)ᗮ, totalVariationOn volume
      (Opens.comap ⟨fun t : ℝ => (y : E) + t • b i, by fun_prop⟩ Ω)
      (fun t : ℝ => u ((y : E) + t • b i)) := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  -- The coordinates `⟪b i, φ⟫` of `φ`, as scalar test functions bounded by one.
  set ψ : ι → 𝓓(Ω, ℝ) := fun i => postcompCLM (innerSL ℝ (b i)) φ
  have hψ (i : ι) (x : E) : ψ i x = ⟪b i, φ x⟫ := by simp [ψ]
  have hψle (i : ι) (x : E) : ‖ψ i x‖ ≤ 1 := by
    rw [hψ, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (by simpa using hφ x)
  have hdiv (x : E) : divergenceCLM φ x = ∑ i, ∂_{b i} (ψ i) x := by
    rw [divergenceCLM_apply_eq_sum b.toBasis]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lineDerivOp_apply]
    congr 1
    ext y
    simp [hψ, OrthonormalBasis.repr_apply_apply]
  have hint (i : ι) : Integrable (fun x => ∂_{b i} (ψ i) x * u x) := by
    simpa using TestFunction.integrable_smul (∂_{b i} (ψ i)) hu
  have hsum : ∫ x, divergenceCLM φ x * u x = ∑ i, ∫ x, ∂_{b i} (ψ i) x * u x := by
    rw [← integral_finsetSum _ fun i _ => hint i]
    simp [hdiv, Finset.sum_mul]
  rw [hsum]
  refine (Finset.le_sum_of_subadditive ENNReal.ofReal ENNReal.ofReal_zero.le
    (fun _ _ => ENNReal.ofReal_add_le) _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact ofReal_integral_lineDerivOp_mul_le_lintegral_totalVariationOn_line hu (b i)
    (b.orthonormal.1 i) (ψ i) (hψle i)

/-- **The converse slicing inequality for perimeter.** For a null-measurable set `s`, an open set
`Ω` and an orthonormal basis `b` of `E`, the perimeter of `s` in `Ω` is at most the sum over `i`
of the integrals, over the hyperplanes `(ℝ ∙ b i)ᗮ`, of the perimeters of the line sections
`{t | y + t • b i ∈ s}` in the open sets `{t | y + t • b i ∈ Ω}`. No finiteness of the volume or
of any perimeter is assumed. -/
theorem perimeter_le_sum_lintegral_perimeter_lineSection {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : Set E} (hs : NullMeasurableSet s) :
    perimeter volume Ω s ≤ ∑ i, ∫⁻ y : (ℝ ∙ b i)ᗮ, perimeter volume
      (Opens.comap ⟨fun t : ℝ => (y : E) + t • b i, by fun_prop⟩ Ω)
      {t : ℝ | (y : E) + t • b i ∈ s} := by
  have hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω :=
    (((locallyIntegrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable volume s)).congr
      (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)).locallyIntegrableOn _
  simp_rw [perimeter_def, ← indicator_one_line]
  exact totalVariationOn_le_sum_lintegral_totalVariationOn_line b hu

/-- **Finite perimeter from the line sections.** If the perimeters of the line sections of a
null-measurable set `s` along the directions of an orthonormal basis, in the open sets of
parameters of the lines lying in `Ω`, have finite integrals over the orthogonal hyperplanes, then
`s` has finite perimeter in `Ω`. -/
theorem perimeter_lt_top_of_lintegral_perimeter_lineSection_lt_top {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : Set E} (hs : NullMeasurableSet s)
    (h : ∀ i, ∫⁻ y : (ℝ ∙ b i)ᗮ, perimeter volume
      (Opens.comap ⟨fun t : ℝ => (y : E) + t • b i, by fun_prop⟩ Ω)
      {t : ℝ | (y : E) + t • b i ∈ s} < ∞) :
    perimeter volume Ω s < ∞ :=
  (perimeter_le_sum_lintegral_perimeter_lineSection b hs).trans_lt
    (ENNReal.sum_lt_top.mpr fun i _ => h i)

end TauCeti
