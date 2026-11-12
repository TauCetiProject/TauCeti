/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Topology.Algebra.InfiniteSum.Automorphize

/-!
# Densities on the additive circle

Reading an additive-circle point in the chart `[a, a + T)` sends circle volume to
restricted Lebesgue measure. For a law with density relative to normalized Haar measure,
the real chart density is the lifted density divided by the period `T`.

These identities allow cdfs and quantiles of circular laws to be computed in a fixed
angle chart, with an explicit choice at the seam. Covering `ℝ` by translates of one chart also
shows that a set of the circle is null exactly when its preimage in `ℝ` is null
(`AddCircle.volume_preimage_coe_eq_zero_iff`).

In the other direction, reducing a real law with density `f` modulo `T` gives the circle law
whose density relative to circle volume is the periodization
`QuotientAddGroup.automorphize f`, which at a real point `x` is `∑ k : ℤ, f (x + k • T)`.
This is how wrapped laws on the circle obtain their densities.

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

/-- A set of the additive circle is null exactly when its preimage in `ℝ` is null. -/
theorem volume_preimage_coe_eq_zero_iff {s : Set (AddCircle T)} :
    volume (((↑) : ℝ → AddCircle T) ⁻¹' s) = 0 ↔ volume s = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- the circle volume of `s` is the real volume of its lift to one period
    -- `measurableEquivIoc T 0` has underlying equivalence `equivIoc T 0`
    have hemb : MeasurableEmbedding (equivIoc T 0) := (measurableEquivIoc T 0).measurableEmbedding
    have h1 := (measurePreserving_equivIoc (T := T) (a := 0)).measure_preimage_emb hemb
      ((equivIoc T 0).symm ⁻¹' s)
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply,
      Equiv.preimage_symm_preimage] at h1
    refine nonpos_iff_eq_zero.1 (h1.trans_le (h ▸ measure_mono ?_))
    -- the inverse of `equivIoc` is the quotient map, so the lift of `y` is `y` itself
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  · -- cover by a measurable null set, then use that the intervals `(k • T, k • T + T]` cover `ℝ`
    have hs : MeasurableSet (toMeasurable volume s) := measurableSet_toMeasurable _ _
    have ht : volume (toMeasurable volume s) = 0 := by rwa [measure_toMeasurable]
    refine measure_mono_null (Set.preimage_mono (subset_toMeasurable volume s)) ?_
    refine measure_mono_null (t := ⋃ k : ℤ, ((↑) : ℝ → AddCircle T) ⁻¹' toMeasurable volume s ∩
        Ioc (k • T) (k • T + T)) (fun x hx ↦ ?_) (measure_iUnion_null fun k ↦ ?_)
    · obtain ⟨k, hk⟩ := mem_iUnion.1 ((iUnion_Ioc_zsmul hT.out).symm ▸ mem_univ x)
      exact mem_iUnion.2 ⟨k, hx, by rwa [← add_one_zsmul]⟩
    · rw [← Measure.restrict_apply' measurableSet_Ioc,
        (AddCircle.measurePreserving_mk T (k • T)).measure_preimage hs.nullMeasurableSet, ht]

/-- The real density in `[a, a + T)` of a Haar-weighted circle law is its lifted Haar
density divided by `T`. -/
theorem map_coe_equivIco_withDensity_haarAddCircle (a : ℝ) {f : AddCircle T → ℝ≥0∞} :
    (haarAddCircle.withDensity f).map (fun θ ↦ (equivIco T a θ : ℝ)) =
      (volume.restrict (Ico a (a + T))).withDensity
        (fun x : ℝ ↦ (ENNReal.ofReal T)⁻¹ * f x) := by
  have hemb : MeasurableEmbedding fun θ : AddCircle T ↦ (equivIco T a θ : ℝ) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ico).comp
      (measurableEquivIco T a).measurableEmbedding
  have hvol : (haarAddCircle : Measure (AddCircle T)) =
      (ENNReal.ofReal T)⁻¹ • volume := by
    rw [volume_eq_smul_haarAddCircle, smul_smul,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hT.out).ne'
        ENNReal.ofReal_ne_top, one_smul]
  have hf : f = (fun x : ℝ ↦ f x) ∘ fun θ : AddCircle T ↦ (equivIco T a θ : ℝ) :=
    funext fun θ ↦ by simp [coe_equivIco]
  have key := hemb.map_withDensity_comp (μ := (volume : Measure (AddCircle T))) fun x : ℝ ↦ f x
  rw [← hf, map_coe_equivIco_volume] at key
  rw [hvol, withDensity_smul_measure, Measure.map_smul, key,
    ← withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (by simpa using hT.out))]
  · rfl
  · exact hemb.measurable.aemeasurable

section Periodization

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M]

/-- The periodization of a function on `ℝ`, evaluated at a real point, is the sum of the
function over the translates of that point by multiples of the period. -/
theorem automorphize_coe (f : ℝ → M) (x : ℝ) :
    QuotientAddGroup.automorphize f (x : AddCircle T) = ∑' k : ℤ, f (x + k • T) := by
  let e : ℤ ≃ (AddSubgroup.zmultiples T).op :=
    (AddSubgroup.zmultiplesEquivInt hT.out.ne').symm.toEquiv.trans (AddSubgroup.equivOp _)
  rw [QuotientAddGroup.automorphize_mk, ← e.tsum_eq]
  refine tsum_congr fun k ↦ congrArg f ?_
  simp [e, AddSubgroup.vadd_def, AddSubgroup.coe_zmultiplesEquivInt_symm_apply]

/-- Reducing a real law with density `f` modulo `T` gives the circle law whose density
relative to circle volume is the periodization of `f`.

The proof is the unfolding argument of `QuotientAddGroup.integral_eq_integral_automorphize`,
carried out for lower integrals of `ℝ≥0∞`-valued functions so that no integrability hypothesis
is needed. -/
theorem map_coe_withDensity {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map ((↑) : ℝ → AddCircle T) =
      volume.withDensity (QuotientAddGroup.automorphize f) := by
  ext A hA
  have hA' : MeasurableSet (((↑) : ℝ → AddCircle T) ⁻¹' A) := AddCircle.measurable_mk' hA
  have hmeas (γ : (AddSubgroup.zmultiples T).op) :
      AEMeasurable (fun x ↦ (((↑) : ℝ → AddCircle T) ⁻¹' A).indicator f (γ +ᵥ x))
        (volume.restrict (Ioc 0 (0 + T))) :=
    ((hf.indicator hA').comp (measurable_const_vadd γ)).aemeasurable
  rw [Measure.map_apply AddCircle.measurable_mk' hA, withDensity_apply _ hA',
    withDensity_apply _ hA, ← lintegral_indicator hA', ← lintegral_indicator hA,
    ← AddCircle.lintegral_preimage (T := T) 0]
  refine ((isAddFundamentalDomain_Ioc' hT.out 0).lintegral_eq_tsum'' _).trans ?_
  rw [← lintegral_tsum hmeas]
  refine setLIntegral_congr_fun measurableSet_Ioc fun x _ ↦ ?_
  have hx (γ : (AddSubgroup.zmultiples T).op) : ((γ +ᵥ x : ℝ) : AddCircle T) = x :=
    QuotientAddGroup.mk_add_of_mem x γ.2
  by_cases h : (x : AddCircle T) ∈ A
  · simp [indicator, hx, h, QuotientAddGroup.automorphize_mk]
  · simp [indicator, hx, h]

end Periodization

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
