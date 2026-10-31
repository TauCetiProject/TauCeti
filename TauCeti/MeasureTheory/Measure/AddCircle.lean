/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Densities in a half-open angle chart

Reading an additive-circle point in the chart `[a, a + T)` sends circle volume to
restricted Lebesgue measure. For a law with density relative to normalized Haar measure,
the real chart density is the lifted density divided by the period `T`.

These identities allow cdfs and quantiles of circular laws to be computed in a fixed
angle chart, with an explicit choice at the seam.

Reading the circle in the symmetric chart `(-T/2, T/2]`, on which the distance to `0` is `|x|`,
also bounds the integral of a radial function `h ↦ g ‖h‖` by twice the integral of `g` over the
half line (`AddCircle.lintegral_comp_norm_le`).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- Reading a circle point in `[a, a + T)` sends circle volume to Lebesgue measure
restricted to that interval. -/
theorem map_coe_equivIco_volume (a : ℝ) :
    (volume : Measure (AddCircle T)).map (fun θ ↦ (equivIco T a θ : ℝ)) =
      volume.restrict (Ico a (a + T)) := by
  have hm : Measurable fun θ ↦ (equivIco T a θ : ℝ) :=
    measurable_subtype_coe.comp (measurableEquivIco T a).measurable
  have hproj : (volume.restrict (Ico a (a + T))).map ((↑) : ℝ → AddCircle T) = volume := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    exact (AddCircle.measurePreserving_mk T a).map_eq
  rw [← hproj, Measure.map_map hm AddCircle.measurable_mk']
  convert (Measure.map_id (μ := volume.restrict (Ico a (a + T)))) using 1
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  exact equivIco_coe_of_mem hx

/-- The real density in `[a, a + T)` of a Haar-weighted circle law is its lifted Haar
density divided by `T`. -/
theorem map_coe_equivIco_withDensity_haarAddCircle (a : ℝ)
    {f : AddCircle T → ℝ≥0∞} (hf : Measurable f) :
    (haarAddCircle.withDensity f).map (fun θ ↦ (equivIco T a θ : ℝ)) =
      (volume.restrict (Ico a (a + T))).withDensity
        (fun x : ℝ ↦ (ENNReal.ofReal T)⁻¹ * f x) := by
  have hmap : (volume.withDensity f).map (fun θ ↦ (equivIco T a θ : ℝ)) =
      (volume.restrict (Ico a (a + T))).withDensity (fun x : ℝ ↦ f x) := by
    refine Measure.map_withDensity_eq_withDensity (jac := fun _ ↦ 1)
      (measurable_subtype_coe.comp (measurableEquivIco T a).measurable)
      measurable_const (hf.comp AddCircle.measurable_mk') ?_ ?_
    · simpa using map_coe_equivIco_volume (T := T) a
    · exact ae_of_all _ fun θ ↦ by simp
  have hvol : (haarAddCircle : Measure (AddCircle T)) =
      (ENNReal.ofReal T)⁻¹ • volume := by
    rw [volume_eq_smul_haarAddCircle, smul_smul,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hT.out).ne'
        ENNReal.ofReal_ne_top, one_smul]
  rw [hvol, withDensity_smul_measure, Measure.map_smul, hmap]
  · exact (withDensity_smul _ (hf.comp AddCircle.measurable_mk')).symm
  · exact (measurable_subtype_coe.comp (measurableEquivIco T a).measurable).aemeasurable

/-- A radial function on the circle integrates to at most twice its integral over the half line:
`∫⁻ h, g ‖h‖ ≤ 2 ∫⁻ t in (0, ∞), g t`. -/
theorem lintegral_comp_norm_le {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ h : AddCircle T, g ‖h‖ ≤ 2 * ∫⁻ t in Ioi 0, g t := by
  have hT0 := hT.out
  rw [← AddCircle.lintegral_preimage T (-(T / 2))]
  calc ∫⁻ x in Ioc (-(T / 2)) (-(T / 2) + T), g ‖((x : ℝ) : AddCircle T)‖
      = ∫⁻ x in Ioc (-(T / 2)) (-(T / 2) + T), g |x| := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
        rw [(norm_coe_eq_abs_iff (p := T) hT0.ne').2]
        rw [abs_of_pos hT0, abs_le]
        constructor <;> linarith [hx.1, hx.2]
    _ ≤ ∫⁻ x, g |x| := setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ x, ((Ici 0).indicator g x + (Ici 0).indicator g (-x)) := by
        refine lintegral_mono fun x ↦ ?_
        rcases le_or_gt 0 x with hx | hx
        · rw [abs_of_nonneg hx, indicator_of_mem (mem_Ici.2 hx)]
          exact le_self_add
        · rw [abs_of_neg hx, indicator_of_mem (mem_Ici.2 (neg_nonneg.2 hx.le))]
          exact le_add_self
    _ = 2 * ∫⁻ t in Ioi 0, g t := by
        rw [lintegral_add_left (hg.indicator measurableSet_Ici),
          lintegral_neg_eq_self fun x ↦ (Ici 0).indicator g x,
          lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici, two_mul]

end AddCircle
