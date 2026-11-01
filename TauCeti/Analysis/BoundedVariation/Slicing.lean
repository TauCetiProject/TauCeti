/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.BoundedVariation.Approximation

/-!
# Slicing functions of bounded variation along parallel lines

Let `E` be a finite-dimensional real inner product space with its volume, and let `e` be a unit
vector. Every point of `E` is uniquely `y + t • e` with `y` in the orthogonal hyperplane
`(ℝ ∙ e)ᗮ` and `t : ℝ` (`TauCeti.orthogonalLineEquiv`). For an integrable function `u`, the
one-dimensional total variations of its restrictions `t ↦ u (y + t • e)` to the lines parallel to
`e` integrate to at most its total variation on the whole space:

`∫_{(ℝ ∙ e)ᗮ} |D(u (y + · • e))|(ℝ) dy ≤ |Du|(E)`

(`TauCeti.lintegral_totalVariationOn_line_le`). If `u` has bounded variation, almost every such
restriction has bounded variation on the line (`TauCeti.ae_totalVariationOn_line_lt_top`). For
a set `s` of finite volume, with the line sections `{t | y + t • e ∈ s}`, this says

`∫_{(ℝ ∙ e)ᗮ} P({t | y + t • e ∈ s}) dy ≤ P(s)`

(`TauCeti.lintegral_perimeter_lineSection_le`), so almost every line section of a set of finite
perimeter has finite perimeter in `ℝ` (`TauCeti.ae_perimeter_lineSection_lt_top`). This is the
inequality half of the slicing theorem for sets of finite perimeter. Combined with the
one-dimensional isoperimetric inequalities of `TauCeti.Analysis.BoundedVariation.Real`, it
controls how many essential boundary points the line sections of a set can have. For instance a
section of perimeter less than `4` agrees almost everywhere with an interval.

For a `C¹` function `w` the line variations are computed exactly: they integrate to
`∫_E |∂_e w|` (`ContDiff.lintegral_totalVariationOn_line_eq`), which is at most
`∫_E ‖Dw‖ = |Dw|(E)`. The general inequality follows by strict approximation
(`MeasureTheory.Integrable.exists_contDiff_hasCompactSupport_strict_approximation`). Along a
subsequence with summable `L¹` errors, Tonelli's theorem in orthogonal line coordinates makes the
restrictions converge in `L¹` on almost every line
(`TauCeti.exists_strictMono_ae_tendsto_lintegral_line`). Lower semicontinuity of the variation
on each such line (`TauCeti.totalVariationOn_le_liminf`) and Fatou's lemma conclude.

## Main results

* `ContDiff.lintegral_totalVariationOn_line_eq`: for `C¹` functions the line variations integrate
  to `∫_E |∂_e w|`.
* `TauCeti.lintegral_totalVariationOn_line_le`: the slicing inequality for integrable functions.
* `TauCeti.ae_totalVariationOn_line_lt_top`: almost every line restriction of an integrable
  function of bounded variation has bounded variation.
* `TauCeti.lintegral_perimeter_lineSection_le` and `TauCeti.ae_perimeter_lineSection_lt_top`: the
  same statements for the line sections of sets of finite volume.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.11 (slicing of functions of bounded variation).
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TauCeti

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The variation of a `C¹` function along the line through `y` in direction `e` is the integral
of the directional derivative along that line. -/
private theorem totalVariationOn_line_eq_lintegral {w : E → ℝ} (hw : ContDiff ℝ 1 w) (y e : E) :
    totalVariationOn volume ⊤ (fun t : ℝ => w (y + t • e)) =
      ∫⁻ t : ℝ, ‖fderiv ℝ w (y + t • e) e‖ₑ := by
  have hc : ContDiff ℝ 1 (fun t : ℝ => w (y + t • e)) :=
    hw.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  rw [hc.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
    Opens.coe_top, Measure.restrict_univ]
  refine lintegral_congr fun t => ?_
  have hl : HasDerivAt (fun s : ℝ => y + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add y
  have hd := ((hw.differentiable one_ne_zero (y + t • e)).hasFDerivAt.comp_hasDerivAt t hl).deriv
  rw [← hd]
  simp only [enorm_eq_nnnorm, ENNReal.coe_inj]
  exact NNReal.eq (norm_deriv_eq_norm_fderiv (f := fun s : ℝ => w (y + s • e))).symm

end TauCeti

/-- **Slicing a `C¹` function.** The total variations of the restrictions of a `C¹` function `w`
to the lines parallel to a unit vector `e` integrate, over the orthogonal hyperplane, to the
integral `∫_E |∂_e w|` of its directional derivative. -/
theorem ContDiff.lintegral_totalVariationOn_line_eq {w : E → ℝ} (hw : ContDiff ℝ 1 w) (e : E)
    (he : ‖e‖ = 1) :
    ∫⁻ y : (ℝ ∙ e)ᗮ, TauCeti.totalVariationOn volume ⊤ (fun t : ℝ => w ((y : E) + t • e)) =
      ∫⁻ x, ‖fderiv ℝ w x e‖ₑ := by
  simp_rw [TauCeti.totalVariationOn_line_eq_lintegral hw]
  exact (TauCeti.lintegral_eq_lintegral_lintegral_line e he
    ((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const).enorm.aemeasurable).symm

namespace TauCeti

/-- For a `C¹` function the line variations integrate to at most its total variation. -/
private theorem lintegral_totalVariationOn_line_le_of_contDiff {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (e : E) (he : ‖e‖ = 1) :
    ∫⁻ y : (ℝ ∙ e)ᗮ, totalVariationOn volume ⊤ (fun t : ℝ => w ((y : E) + t • e)) ≤
      totalVariationOn volume ⊤ w := by
  rw [hw.lintegral_totalVariationOn_line_eq e he,
    hw.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
    Opens.coe_top, Measure.restrict_univ]
  exact lintegral_mono fun x => enorm_le_iff_norm_le.mpr <| by
    simpa [he] using (fderiv ℝ w x).le_opNorm e

/-- The line variations of an integrable function are bounded almost everywhere by an a.e.
measurable function whose integral is at most the total variation. -/
private theorem exists_aemeasurable_totalVariationOn_line_le {u : E → ℝ} (hu : Integrable u)
    (e : E) (he : ‖e‖ = 1) :
    ∃ G : (ℝ ∙ e)ᗮ → ℝ≥0∞, AEMeasurable G ∧
      (∀ᵐ y : (ℝ ∙ e)ᗮ, totalVariationOn volume ⊤ (fun t : ℝ => u ((y : E) + t • e)) ≤ G y) ∧
      ∫⁻ y, G y ≤ totalVariationOn volume ⊤ u := by
  obtain ⟨w, hw, hL1, hTV⟩ :=
    hu.exists_contDiff_hasCompactSupport_strict_approximation (μ := volume)
  have hw1 (n : ℕ) : ContDiff ℝ 1 (w n) := (hw n).1.of_le (by simp)
  obtain ⟨φ, hφ, hFlim⟩ := exists_strictMono_ae_tendsto_lintegral_line e he
    (fun n => ((hw n).1.continuous.aestronglyMeasurable.sub hu.aestronglyMeasurable).enorm) hL1
  -- Almost every line restriction of `u` is integrable, by Fubini's theorem.
  have hline : ∀ᵐ y : (ℝ ∙ e)ᗮ, Integrable (fun t : ℝ => u ((y : E) + t • e)) := by
    simpa only [Function.comp_def, orthogonalLineEquiv_apply] using
      ((measurePreserving_orthogonalLineEquiv e he).integrable_comp_of_integrable hu).prod_right_ae
  -- The line variations of the approximations, as a.e. measurable functions of `y`.
  let V (j : ℕ) (y : (ℝ ∙ e)ᗮ) : ℝ≥0∞ :=
    totalVariationOn volume ⊤ (fun t : ℝ => w (φ j) ((y : E) + t • e))
  have hVm (j : ℕ) : AEMeasurable (V j) := by
    simp_rw [V, totalVariationOn_line_eq_lintegral (hw1 _)]
    exact aemeasurable_lintegral_line e he
      (((hw1 _).continuous_fderiv one_ne_zero).clm_apply continuous_const).enorm.aemeasurable
  refine ⟨fun y => liminf (fun j => V j y) atTop, AEMeasurable.liminf hVm, ?_, ?_⟩
  · -- On almost every line the restrictions converge in `L¹`; the variation is l.s.c.
    filter_upwards [hFlim, hline] with y hy hyi
    refine totalVariationOn_le_liminf
      (.of_forall fun j => ((hw _).1.continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))).locallyIntegrable.locallyIntegrableOn _)
      (hyi.locallyIntegrable.locallyIntegrableOn _) fun K _ _ => ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hy (fun _ => zero_le)
      fun j => setLIntegral_le_lintegral _ _
  · -- Fatou's lemma and the `C¹` case.
    calc ∫⁻ y, liminf (fun j => V j y) atTop ≤ liminf (fun j => ∫⁻ y, V j y) atTop :=
          lintegral_liminf_le' hVm
      _ ≤ liminf (fun j => totalVariationOn volume ⊤ (w (φ j))) atTop :=
          liminf_le_liminf (.of_forall fun j =>
            lintegral_totalVariationOn_line_le_of_contDiff (hw1 _) e he)
      _ = totalVariationOn volume ⊤ u := (hTV.comp hφ.tendsto_atTop).liminf_eq

/-- **The slicing inequality for functions of bounded variation.** For an integrable function `u`
and a unit vector `e`, the total variations of the restrictions `t ↦ u (y + t • e)` to the lines
parallel to `e` integrate, over the orthogonal hyperplane, to at most the total variation of `u`:
`∫_{(ℝ ∙ e)ᗮ} |D(u (y + · • e))|(ℝ) dy ≤ |Du|(E)`. -/
theorem lintegral_totalVariationOn_line_le {u : E → ℝ} (hu : Integrable u) (e : E)
    (he : ‖e‖ = 1) :
    ∫⁻ y : (ℝ ∙ e)ᗮ, totalVariationOn volume ⊤ (fun t : ℝ => u ((y : E) + t • e)) ≤
      totalVariationOn volume ⊤ u := by
  obtain ⟨G, -, hG, hGint⟩ := exists_aemeasurable_totalVariationOn_line_le hu e he
  exact (lintegral_mono_ae hG).trans hGint

/-- If an integrable function has bounded variation, then its restrictions to almost all lines
parallel to a unit vector `e` have bounded variation on the line. -/
theorem ae_totalVariationOn_line_lt_top {u : E → ℝ} (hu : Integrable u)
    (hV : totalVariationOn volume ⊤ u ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ, totalVariationOn volume ⊤ (fun t : ℝ => u ((y : E) + t • e)) < ∞ := by
  obtain ⟨G, hGm, hG, hGint⟩ := exists_aemeasurable_totalVariationOn_line_le hu e he
  filter_upwards [hG, ae_lt_top' hGm (ne_top_of_le_ne_top hV hGint)] with y h₁ h₂
  exact h₁.trans_lt h₂

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The restriction of an indicator to a line is the indicator of the line section. -/
private theorem indicator_one_line (s : Set E) (y e : E) :
    (fun t : ℝ => s.indicator (1 : E → ℝ) (y + t • e)) =
      {t : ℝ | y + t • e ∈ s}.indicator 1 :=
  funext fun _ => (indicator_comp_right (fun t : ℝ => y + t • e)).symm

private theorem integrable_indicator_one {s : Set E} (hs : NullMeasurableSet s)
    (hfin : volume s ≠ ∞) : Integrable (s.indicator (1 : E → ℝ)) :=
  (integrableOn_const hfin).integrable_indicator₀ hs

/-- **The slicing inequality for perimeter.** For a null-measurable set `s` of finite volume and
a unit vector `e`, the perimeters in `ℝ` of the line sections `{t | y + t • e ∈ s}` integrate,
over the orthogonal hyperplane, to at most the perimeter of `s`. -/
theorem lintegral_perimeter_lineSection_le {s : Set E} (hs : NullMeasurableSet s)
    (hfin : volume s ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    ∫⁻ y : (ℝ ∙ e)ᗮ, perimeter volume ⊤ {t : ℝ | (y : E) + t • e ∈ s} ≤
      perimeter volume ⊤ s := by
  simp_rw [perimeter_def, ← indicator_one_line]
  exact lintegral_totalVariationOn_line_le (integrable_indicator_one hs hfin) e he

/-- Almost every line section of a set of finite volume and finite perimeter has finite
perimeter in `ℝ`. -/
theorem ae_perimeter_lineSection_lt_top {s : Set E} (hs : NullMeasurableSet s)
    (hfin : volume s ≠ ∞) (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ, perimeter volume ⊤ {t : ℝ | (y : E) + t • e ∈ s} < ∞ := by
  rw [perimeter_def] at hP
  simp_rw [perimeter_def, ← indicator_one_line]
  exact ae_totalVariationOn_line_lt_top (integrable_indicator_one hs hfin) hP e he

end TauCeti
