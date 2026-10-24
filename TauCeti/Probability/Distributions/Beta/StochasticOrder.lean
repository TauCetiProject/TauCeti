/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Cdf
public import TauCeti.Probability.StochasticOrder
import TauCeti.Probability.Distributions.Gamma.Beta

/-!
# Stochastic comparison of Beta laws

Increasing the first positive shape or decreasing the second positive shape increases a Beta
law in first-order stochastic order. We give the reversed cdf inequalities, the corresponding
interior quantile inequality, and the almost-sure order of the common-uniform quantile coupling.

These comparisons transfer probability and quantile bounds between Beta laws with ordered
shape parameters.

## References

* M. Shaked and J. G. Shanthikumar, *Stochastic Orders*, Springer, 2007, Chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- Increasing the first positive Beta shape decreases the cdf. -/
theorem cdf_betaMeasure_le_of_le_left {a₁ a₂ b : ℝ} (ha₁ : 0 < a₁) (hb : 0 < b)
    (ha : a₁ ≤ a₂) (x : ℝ) : cdf (betaMeasure a₂ b) x ≤ cdf (betaMeasure a₁ b) x := by
  obtain rfl | ha := ha.eq_or_lt
  · exact le_rfl
  have hd : 0 < a₂ - a₁ := sub_pos.mpr ha
  let _ := isProbabilityMeasure_gammaMeasure ha₁ one_pos
  let _ := isProbabilityMeasure_gammaMeasure hd one_pos
  let _ := isProbabilityMeasure_gammaMeasure hb one_pos
  let P := ((gammaMeasure a₁ 1).prod (gammaMeasure (a₂ - a₁) 1)).prod (gammaMeasure b 1)
  have hpair : HasLaw Prod.fst
      ((gammaMeasure a₁ 1).prod (gammaMeasure (a₂ - a₁) 1)) P :=
    measurePreserving_fst.hasLaw
  have hfirst : HasLaw (fun z : (ℝ × ℝ) × ℝ ↦ z.1.1) (gammaMeasure a₁ 1) P :=
    measurePreserving_fst.hasLaw.fun_comp hpair
  have hincrement : HasLaw (fun z : (ℝ × ℝ) × ℝ ↦ z.1.2)
      (gammaMeasure (a₂ - a₁) 1) P := measurePreserving_snd.hasLaw.fun_comp hpair
  have hlast : HasLaw Prod.snd (gammaMeasure b 1) P := measurePreserving_snd.hasLaw
  have hsum : HasLaw (fun z : ℝ × ℝ ↦ z.1 + z.2) (gammaMeasure a₂ 1)
      ((gammaMeasure a₁ 1).prod (gammaMeasure (a₂ - a₁) 1)) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [Measure.conv, add_sub_cancel] using
      gammaMeasure_conv_gammaMeasure ha₁ hd one_pos
  have hsmall := hasLaw_div_add_gammaMeasure_of_indepFun ha₁ hb one_pos
    (indepFun_prod measurable_fst measurable_id) hfirst hlast
  have hlarge := hasLaw_div_add_gammaMeasure_of_indepFun (ha₁.trans ha) hb one_pos
    (indepFun_prod (measurable_fst.add measurable_snd) measurable_id)
    (hsum.fun_comp hpair) hlast
  apply hsmall.cdf_le_of_ae_le hlarge _ x
  have hfirst_pos : ∀ᵐ z ∂P, 0 < z.1.1 := by
    apply ae_of_ae_map hfirst.aemeasurable
    rw [hfirst.map_eq]
    exact ae_pos_gammaMeasure a₁ 1
  have hincrement_pos : ∀ᵐ z ∂P, 0 < z.1.2 := by
    apply ae_of_ae_map hincrement.aemeasurable
    rw [hincrement.map_eq]
    exact ae_pos_gammaMeasure (a₂ - a₁) 1
  have hlast_pos : ∀ᵐ z ∂P, 0 < z.2 := by
    apply ae_of_ae_map hlast.aemeasurable
    rw [hlast.map_eq]
    exact ae_pos_gammaMeasure b 1
  filter_upwards [hfirst_pos, hincrement_pos, hlast_pos] with z hz₁ hz₂ hz₃
  simp only [Pi.add_apply, id_eq]
  apply (div_le_div_iff₀ (add_pos hz₁ hz₃) (add_pos (add_pos hz₁ hz₂) hz₃)).2
  nlinarith [mul_nonneg hz₂.le hz₃.le]

/-- Increasing the second positive Beta shape increases the cdf. -/
theorem cdf_betaMeasure_le_of_le_right {a b₁ b₂ : ℝ} (ha : 0 < a) (hb₁ : 0 < b₁)
    (hb : b₁ ≤ b₂) (x : ℝ) : cdf (betaMeasure a b₁) x ≤ cdf (betaMeasure a b₂) x := by
  have h := cdf_betaMeasure_le_of_le_left hb₁ ha hb (1 - x)
  rw [cdf_betaMeasure_eq hb₁ ha, cdf_betaMeasure_eq (hb₁.trans_le hb) ha] at h
  rw [cdf_betaMeasure_eq ha hb₁, cdf_betaMeasure_eq ha (hb₁.trans_le hb),
    regularizedIncompleteBeta_symm ha hb₁,
    regularizedIncompleteBeta_symm ha (hb₁.trans_le hb)]
  exact sub_le_sub_left h 1

/-- Increasing the first shape and decreasing the second shape decreases the Beta cdf. -/
theorem cdf_betaMeasure_le {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : 0 < a₁) (hb₂ : 0 < b₂)
    (ha : a₁ ≤ a₂) (hb : b₂ ≤ b₁) (x : ℝ) :
    cdf (betaMeasure a₂ b₂) x ≤ cdf (betaMeasure a₁ b₁) x :=
  (cdf_betaMeasure_le_of_le_left ha₁ hb₂ ha x).trans
    (cdf_betaMeasure_le_of_le_right ha₁ hb₂ hb x)

/-- Beta quantiles increase when the first shape increases and the second shape decreases. -/
theorem quantile_betaMeasure_le {a₁ a₂ b₁ b₂ u : ℝ} (ha₁ : 0 < a₁) (hb₂ : 0 < b₂)
    (ha : a₁ ≤ a₂) (hb : b₂ ≤ b₁) (hu : u ∈ Ioo (0 : ℝ) 1) :
    (betaMeasure a₁ b₁).quantile u ≤ (betaMeasure a₂ b₂).quantile u :=
  (Measure.cdf_le_iff_quantile_le _ _).1 (cdf_betaMeasure_le ha₁ hb₂ ha hb) u hu.1 hu.2

/-- The common-uniform coupling of Beta laws is almost surely ordered when the first shape
increases and the second shape decreases. Its marginals are the two Beta laws by
`MeasureTheory.Measure.isCoupling_quantileCoupling`. -/
theorem ae_fst_le_snd_quantileCoupling_betaMeasure {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 < a₁) (hb₂ : 0 < b₂) (ha : a₁ ≤ a₂) (hb : b₂ ≤ b₁) :
    ∀ᵐ z ∂(betaMeasure a₁ b₁).quantileCoupling (betaMeasure a₂ b₂), z.1 ≤ z.2 := by
  let _ := isProbabilityMeasureBeta ha₁ (hb₂.trans_le hb)
  let _ := isProbabilityMeasureBeta (ha₁.trans_le ha) hb₂
  exact Measure.ae_fst_le_snd_quantileCoupling _ _ (cdf_betaMeasure_le ha₁ hb₂ ha hb)

end TauCeti.Probability
