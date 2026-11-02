/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import TauCeti.Analysis.BoundedVariation.Approximation
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine
import TauCeti.Analysis.Sobolev.WeakDeriv.Slicing

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

The inequality holds jointly with the transverse variation. For a test vector field `φ` on
`(ℝ ∙ e)ᗮ` with `‖φ‖ ≤ 1`,

`∫ √(1 - ‖φ‖²) |D(u (y + · • e))|(ℝ) dy + ∫ div φ (y) ∫ u (y + t • e) dt dy ≤ |Du|(E)`

(`TauCeti.lintegral_mul_totalVariationOn_line_add_ofReal_integral_le`). Taking `φ = 0` gives the
slicing inequality, and dropping the first term shows that integrating along the lines does not
increase variation (`TauCeti.totalVariationOn_integral_line_le`). For a set `s` the line integrals
are the lengths `|{t | y + t • e ∈ s}|` of the sections, so these lengths have total variation at
most `P(s)` (`TauCeti.totalVariationOn_measureReal_lineSection_le`), and
`TauCeti.lintegral_mul_perimeter_lineSection_add_ofReal_integral_le` bounds `P(s)` below jointly by
the section perimeters and the variation of the section lengths. The section lengths are exactly
what Steiner symmetrization along `e` preserves, so this is the lower bound in the comparison of
perimeters under Steiner symmetrization.

For a `C¹` function `w` the line variations are computed exactly: they integrate to
`∫_E |∂_e w|` (`ContDiff.lintegral_totalVariationOn_line_eq`), which is at most
`∫_E ‖Dw‖ = |Dw|(E)`. In the joint inequality the transverse term of a `C¹` function is
`-∫_E Dw (φ (y))`, by integration by parts on each hyperplane
(`TauCeti.integral_divergence_mul_integral_line_eq`), and
`√(1 - ‖φ‖²) |∂_e w| - Dw (φ) ≤ ‖Dw‖` pointwise because `±√(1 - ‖φ‖²) e - φ` is a unit vector
(`TauCeti.sqrt_mul_abs_apply_sub_apply_le`). The transverse term passes to the limit by `L¹`
continuity of the pairing (`TauCeti.tendsto_integral_mul_integral_line`).
The general inequality follows by strict approximation
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
* `TauCeti.lintegral_mul_totalVariationOn_line_add_ofReal_integral_le`: the joint slicing
  inequality, with the transverse variation of the line integrals.
* `TauCeti.totalVariationOn_integral_line_le`: integrating along lines does not increase variation.
* `TauCeti.lintegral_mul_perimeter_lineSection_add_ofReal_integral_le` and
  `TauCeti.totalVariationOn_measureReal_lineSection_le`: the joint inequality for sets, and bounded
  variation of the lengths of the line sections.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.11 (slicing of functions of bounded variation).
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 14 (the
  lengths of the sections of a set of finite perimeter, and Steiner's inequality).
-/

public section

open MeasureTheory Filter Set TopologicalSpace TestFunction
open scoped ENNReal Topology Distributions

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

/-- **The joint slicing inequality for `C¹` functions.** -/
private theorem lintegral_mul_totalVariationOn_line_add_le_of_contDiff {w : E → ℝ}
    (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) (e : E) (he : ‖e‖ = 1)
    (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    (∫⁻ y : (ℝ ∙ e)ᗮ, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) *
        totalVariationOn volume ⊤ (fun t : ℝ => w ((y : E) + t • e))) +
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y * ∫ t : ℝ, w ((y : E) + t • e)) ≤
      totalVariationOn volume ⊤ w := by
  have hL := measurePreserving_orthogonalLineEquiv e he
  have hLe : MeasurableEmbedding (orthogonalLineEquiv e he) :=
    (orthogonalLineEquiv e he).toHomeomorph.measurableEmbedding
  set L := orthogonalLineEquiv e he
  have hD : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hc : Continuous fun y : (ℝ ∙ e)ᗮ => √(1 - ‖φ y‖ ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (φ.continuous.norm.pow 2))
  have hc1 (y : (ℝ ∙ e)ᗮ) : √(1 - ‖φ y‖ ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith [norm_nonneg (φ y)])
  -- The three integrands, in orthogonal line coordinates.
  set F : (ℝ ∙ e)ᗮ × ℝ → ℝ := fun p => √(1 - ‖φ p.1‖ ^ 2) * |fderiv ℝ w (L p) e|
  set G : (ℝ ∙ e)ᗮ × ℝ → ℝ := fun p => -fderiv ℝ w (L p) (φ p.1)
  set N : (ℝ ∙ e)ᗮ × ℝ → ℝ := fun p => ‖fderiv ℝ w (L p)‖
  have hN : Integrable N (volume.prod volume) :=
    hL.integrable_comp_of_integrable
      (hD.norm.integrable_of_hasCompactSupport (hwc.fderiv (𝕜 := ℝ)).norm)
  have hFle (p) : F p ≤ N p := by
    calc F p ≤ 1 * |fderiv ℝ w (L p) e| := mul_le_mul_of_nonneg_right (hc1 p.1) (abs_nonneg _)
      _ ≤ N p := by simpa [N, he] using (fderiv ℝ w (L p)).le_opNorm e
  have hF : Integrable F (volume.prod volume) :=
    hN.mono' ((hc.comp continuous_fst).mul
      ((hD.comp L.continuous).clm_apply continuous_const).abs).aestronglyMeasurable
      (.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hFle p)
  have hFG (p) : F p + G p ≤ N p := sqrt_mul_abs_apply_sub_apply_le e he _ (hφ p.1)
  have hG : Integrable G (volume.prod volume) :=
    hN.mono' ((hD.comp L.continuous).clm_apply
      ((continuous_subtype_val.comp φ.continuous).comp continuous_fst)).neg.aestronglyMeasurable
      (.of_forall fun p => by
        simpa [G, N] using ((fderiv ℝ w (L p)).le_opNorm_of_le (by simpa using hφ p.1)).trans_eq
          (mul_one _))
  -- The first term is `∫ F`, the second `∫ G` and the right side `∫ N`.
  have h₁ : ∫⁻ y : (ℝ ∙ e)ᗮ, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) *
      totalVariationOn volume ⊤ (fun t : ℝ => w ((y : E) + t • e)) =
      ENNReal.ofReal (∫ p, F p ∂(volume.prod volume)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hF (.of_forall fun p => by positivity),
      lintegral_prod _ (hF.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    refine lintegral_congr fun y => ?_
    rw [totalVariationOn_line_eq_lintegral hw, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun t => ?_
    simp only [F, L, orthogonalLineEquiv_apply]
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.enorm_eq_ofReal_abs]
  have h₂ : ∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y * ∫ t : ℝ, w ((y : E) + t • e) =
      ∫ p, G p ∂(volume.prod volume) := by
    rw [integral_divergence_mul_integral_line_eq hw hwc e he φ, integral_neg]
  have h₃ : totalVariationOn volume ⊤ w = ENNReal.ofReal (∫ p, N p ∂(volume.prod volume)) := by
    rw [hw.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
      Opens.coe_top, Measure.restrict_univ,
      ofReal_integral_eq_lintegral_ofReal hN (.of_forall fun p => norm_nonneg _),
      ← hL.lintegral_comp_emb hLe]
    simp [N, ofReal_norm]
  rw [h₁, h₂, h₃]
  rcases le_total 0 (∫ p, G p ∂(volume.prod volume)) with hG0 | hG0
  · rw [← ENNReal.ofReal_add (integral_nonneg fun p => by positivity) hG0, ← integral_add hF hG]
    exact ENNReal.ofReal_le_ofReal (integral_mono (hF.add hG) hN hFG)
  · rw [ENNReal.ofReal_of_nonpos hG0, add_zero]
    exact ENNReal.ofReal_le_ofReal (integral_mono hF hN hFle)

/-- The line variations of an integrable function are bounded almost everywhere by an a.e.
measurable function `G` whose weighted integral, together with the pairing of the line integrals
with a transverse test vector field `φ`, is at most the total variation. -/
private theorem exists_aemeasurable_totalVariationOn_line_le {u : E → ℝ} (hu : Integrable u)
    (e : E) (he : ‖e‖ = 1) (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    ∃ G : (ℝ ∙ e)ᗮ → ℝ≥0∞, AEMeasurable G ∧
      (∀ᵐ y : (ℝ ∙ e)ᗮ, totalVariationOn volume ⊤ (fun t : ℝ => u ((y : E) + t • e)) ≤ G y) ∧
      (∫⁻ y, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) * G y) +
        ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y * ∫ t : ℝ, u ((y : E) + t • e)) ≤
        totalVariationOn volume ⊤ u := by
  obtain ⟨w, hw, hL1, hTV⟩ :=
    hu.exists_contDiff_hasCompactSupport_strict_approximation (μ := volume)
  have hw1 (n : ℕ) : ContDiff ℝ 1 (w n) := (hw n).1.of_le (by simp)
  obtain ⟨σ, hσ, hFlim⟩ := exists_strictMono_ae_tendsto_lintegral_line e he
    (fun n => ((hw n).1.continuous.aestronglyMeasurable.sub hu.aestronglyMeasurable).enorm) hL1
  -- Almost every line restriction of `u` is integrable, by Fubini's theorem.
  have hline : ∀ᵐ y : (ℝ ∙ e)ᗮ, Integrable (fun t : ℝ => u ((y : E) + t • e)) := by
    simpa only [Function.comp_def, orthogonalLineEquiv_apply] using
      ((measurePreserving_orthogonalLineEquiv e he).integrable_comp_of_integrable hu).prod_right_ae
  -- The line variations of the approximations, as a.e. measurable functions of `y`.
  let V (j : ℕ) (y : (ℝ ∙ e)ᗮ) : ℝ≥0∞ :=
    totalVariationOn volume ⊤ (fun t : ℝ => w (σ j) ((y : E) + t • e))
  have hVm (j : ℕ) : AEMeasurable (V j) := by
    simp_rw [V, totalVariationOn_line_eq_lintegral (hw1 _)]
    exact aemeasurable_lintegral_line e he
      (((hw1 _).continuous_fderiv one_ne_zero).clm_apply continuous_const).enorm.aemeasurable
  -- The transverse weight `√(1 - ‖φ‖²)`.
  set c : (ℝ ∙ e)ᗮ → ℝ≥0∞ := fun y => ENNReal.ofReal √(1 - ‖φ y‖ ^ 2)
  have hcm : AEMeasurable c := (ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp
    (continuous_const.sub (φ.continuous.norm.pow 2)))).measurable.aemeasurable
  -- The pairings with `div φ` converge, by `L¹` convergence of the approximations.
  obtain ⟨C, hC⟩ := (divergenceCLM φ).continuous.bounded_above_of_compact_support
    (divergenceCLM φ).hasCompactSupport
  have hB := tendsto_integral_mul_integral_line
    (fun n => (hw (σ n)).1.continuous.integrable_of_hasCompactSupport (hw (σ n)).2) hu
    (hL1.comp hσ.tendsto_atTop) e he (divergenceCLM φ).continuous.aestronglyMeasurable hC
  refine ⟨fun y => liminf (fun j => V j y) atTop, AEMeasurable.liminf hVm, ?_, ?_⟩
  · -- On almost every line the restrictions converge in `L¹`; the variation is l.s.c.
    filter_upwards [hFlim, hline] with y hy hyi
    refine totalVariationOn_le_liminf
      (.of_forall fun j => ((hw _).1.continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))).locallyIntegrable.locallyIntegrableOn _)
      (hyi.locallyIntegrable.locallyIntegrableOn _) fun K _ _ => ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hy (fun _ => zero_le)
      fun j => setLIntegral_le_lintegral _ _
  · -- Fatou's lemma for the weighted variations, and the `C¹` case.
    set A : ℕ → ℝ≥0∞ := fun j => ∫⁻ y, c y * V j y
    set b : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal
      (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y * ∫ t : ℝ, w (σ j) ((y : E) + t • e))
    set B := ENNReal.ofReal
      (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y * ∫ t : ℝ, u ((y : E) + t • e))
    have hFatou : ∫⁻ y, c y * liminf (fun j => V j y) atTop ≤ liminf A atTop := by
      refine (lintegral_mono fun y => ?_).trans (lintegral_liminf_le' fun j => hcm.mul (hVm j))
      simpa only [liminf_const, Pi.mul_def] using
        ENNReal.le_liminf_mul (u := fun _ : ℕ => c y) (v := fun j => V j y) (f := atTop)
    -- The pairings converge, so the defect `B - b j` tends to zero.
    have hb : Tendsto (fun j => B - b j) atTop (𝓝 0) := by
      have hBfinite : B ≠ ∞ := ENNReal.ofReal_ne_top
      have h := ENNReal.Tendsto.sub tendsto_const_nhds
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hB) (Or.inl hBfinite)
      rwa [tsub_self] at h
    calc (∫⁻ y, c y * liminf (fun j => V j y) atTop) + B ≤ liminf A atTop + B := by gcongr
      _ = liminf (fun j => A j + B) atTop := (liminf_add_const atTop A B
          (by isBoundedDefault) (by isBoundedDefault)).symm
      _ ≤ liminf ((fun j => A j + b j) + fun j => B - b j) atTop :=
          liminf_le_liminf (.of_forall fun j => by
            rw [Pi.add_apply, add_assoc]
            gcongr
            exact le_add_tsub)
      _ = liminf (fun j => A j + b j) atTop := ENNReal.liminf_add_of_right_tendsto_zero hb _
      _ ≤ liminf (fun j => totalVariationOn volume ⊤ (w (σ j))) atTop :=
          liminf_le_liminf (.of_forall fun j =>
            lintegral_mul_totalVariationOn_line_add_le_of_contDiff (hw1 _) (hw _).2 e he φ hφ)
      _ = totalVariationOn volume ⊤ u := (hTV.comp hσ.tendsto_atTop).liminf_eq

/-- **The joint slicing inequality for functions of bounded variation.** Let `u` be integrable,
`e` a unit vector and `φ` a test vector field on the orthogonal hyperplane `(ℝ ∙ e)ᗮ` with
`‖φ‖ ≤ 1`. Then the variations `|D(u (y + · • e))|(ℝ)` of the restrictions of `u` to the lines
parallel to `e`, weighted by `√(1 - ‖φ y‖²)`, together with the pairing of the line integrals
`y ↦ ∫ u (y + t • e) dt` with `div φ`, are at most the total variation of `u`:

`∫ √(1 - ‖φ‖²) |D(u (y + · • e))|(ℝ) dy + ∫ div φ (y) ∫ u (y + t • e) dt dy ≤ |Du|(E)`.

For `φ = 0` this is `TauCeti.lintegral_totalVariationOn_line_le`, and dropping the first term
gives `TauCeti.totalVariationOn_integral_line_le`. In general the first term controls the
variation of `u` along `e` and the second the transverse variation of the line integrals, and the
bound holds for both simultaneously. -/
theorem lintegral_mul_totalVariationOn_line_add_ofReal_integral_le {u : E → ℝ}
    (hu : Integrable u) (e : E) (he : ‖e‖ = 1) (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    (∫⁻ y : (ℝ ∙ e)ᗮ, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) *
        totalVariationOn volume ⊤ (fun t : ℝ => u ((y : E) + t • e))) +
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ, divergenceCLM φ y * ∫ t : ℝ, u ((y : E) + t • e)) ≤
      totalVariationOn volume ⊤ u := by
  obtain ⟨G, -, hG, hGint⟩ := exists_aemeasurable_totalVariationOn_line_le hu e he φ hφ
  exact (add_le_add (lintegral_mono_ae (hG.mono fun y hy => by gcongr)) le_rfl).trans hGint

/-- **The slicing inequality for functions of bounded variation.** For an integrable function `u`
and a unit vector `e`, the total variations of the restrictions `t ↦ u (y + t • e)` to the lines
parallel to `e` integrate, over the orthogonal hyperplane, to at most the total variation of `u`:
`∫_{(ℝ ∙ e)ᗮ} |D(u (y + · • e))|(ℝ) dy ≤ |Du|(E)`. -/
theorem lintegral_totalVariationOn_line_le {u : E → ℝ} (hu : Integrable u) (e : E)
    (he : ‖e‖ = 1) :
    ∫⁻ y : (ℝ ∙ e)ᗮ, totalVariationOn volume ⊤ (fun t : ℝ => u ((y : E) + t • e)) ≤
      totalVariationOn volume ⊤ u := by
  simpa using lintegral_mul_totalVariationOn_line_add_ofReal_integral_le hu e he 0 (by simp)

/-- **Integrating along lines does not increase variation.** For an integrable function `u` and a
unit vector `e`, the function `y ↦ ∫ u (y + t • e) dt` on the orthogonal hyperplane `(ℝ ∙ e)ᗮ` has
total variation at most that of `u`. -/
theorem totalVariationOn_integral_line_le {u : E → ℝ} (hu : Integrable u) (e : E)
    (he : ‖e‖ = 1) :
    totalVariationOn volume ⊤ (fun y : (ℝ ∙ e)ᗮ => ∫ t : ℝ, u ((y : E) + t • e)) ≤
      totalVariationOn volume ⊤ u :=
  totalVariationOn_le_iff.mpr fun φ hφ =>
    le_add_self.trans (lintegral_mul_totalVariationOn_line_add_ofReal_integral_le hu e he φ hφ)

/-- If an integrable function has bounded variation, then its restrictions to almost all lines
parallel to a unit vector `e` have bounded variation on the line. -/
theorem ae_totalVariationOn_line_lt_top {u : E → ℝ} (hu : Integrable u)
    (hV : totalVariationOn volume ⊤ u ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ, totalVariationOn volume ⊤ (fun t : ℝ => u ((y : E) + t • e)) < ∞ := by
  obtain ⟨G, hGm, hG, hGint⟩ := exists_aemeasurable_totalVariationOn_line_le hu e he 0 (by simp)
  replace hGint : ∫⁻ y, G y ≤ totalVariationOn volume ⊤ u := by simpa using hGint
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

/-- **The joint slicing inequality for perimeter.** Let `s` be a null-measurable set of finite
volume, `e` a unit vector and `φ` a test vector field on the orthogonal hyperplane `(ℝ ∙ e)ᗮ` with
`‖φ‖ ≤ 1`. The perimeters of the line sections `{t | y + t • e ∈ s}`, weighted by
`√(1 - ‖φ y‖²)`, together with the pairing of their lengths with `div φ`, are at most the
perimeter of `s`:

`∫ √(1 - ‖φ‖²) P({t | y + t • e ∈ s}) dy + ∫ div φ (y) |{t | y + t • e ∈ s}| dy ≤ P(s)`.

This bounds `P(s)` below jointly by the perimeters and by the variation of the lengths of the line
sections, which is the slicing side of the comparison of perimeters under Steiner
symmetrization. -/
theorem lintegral_mul_perimeter_lineSection_add_ofReal_integral_le {s : Set E}
    (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    (φ : 𝓓(⊤, (ℝ ∙ e)ᗮ)) (hφ : ∀ y, ‖φ y‖ ≤ 1) :
    (∫⁻ y : (ℝ ∙ e)ᗮ, ENNReal.ofReal √(1 - ‖φ y‖ ^ 2) *
        perimeter volume ⊤ {t : ℝ | (y : E) + t • e ∈ s}) +
      ENNReal.ofReal (∫ y : (ℝ ∙ e)ᗮ,
        divergenceCLM φ y * volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≤
      perimeter volume ⊤ s := by
  have h := lintegral_mul_totalVariationOn_line_add_ofReal_integral_le
    (integrable_indicator_one hs hfin) e he φ hφ
  simp_rw [indicator_one_line, ← perimeter_def] at h
  have hv : (fun y : (ℝ ∙ e)ᗮ => divergenceCLM φ y * volume.real {t : ℝ | (y : E) + t • e ∈ s})
      =ᵐ[volume] fun y => divergenceCLM φ y *
        ∫ t : ℝ, {t : ℝ | (y : E) + t • e ∈ s}.indicator 1 t := by
    filter_upwards [ae_nullMeasurableSet_lineSection e he hs] with y hy
    rw [integral_indicator₀ hy]
    simp
  rw [integral_congr_ae hv]
  exact h

/-- **The lengths of the line sections of a set of finite perimeter have bounded variation.** For
a null-measurable set `s` of finite volume and a unit vector `e`, the function
`y ↦ |{t | y + t • e ∈ s}|` on the orthogonal hyperplane `(ℝ ∙ e)ᗮ` has total variation at most
the perimeter of `s`. -/
theorem totalVariationOn_measureReal_lineSection_le {s : Set E} (hs : NullMeasurableSet s)
    (hfin : volume s ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    totalVariationOn volume ⊤ (fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) ≤
      perimeter volume ⊤ s :=
  totalVariationOn_le_iff.mpr fun φ hφ => le_add_self.trans
    (lintegral_mul_perimeter_lineSection_add_ofReal_integral_le hs hfin e he φ hφ)

end TauCeti
