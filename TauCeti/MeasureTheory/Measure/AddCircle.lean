/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Densities on the additive circle

Reading an additive-circle point in the chart `[a, a + T)` sends circle volume to
restricted Lebesgue measure. For a law with density relative to normalized Haar measure,
the real chart density is the lifted density divided by the period `T`.

These identities allow cdfs and quantiles of circular laws to be computed in a fixed
angle chart, with an explicit choice at the seam.

In the other direction, reducing a real law with density `f` modulo `T` gives the circle law
whose density relative to circle volume is the periodization
`QuotientAddGroup.automorphize f`, which at a real point `x` is `∑ k : ℤ, f (x + k • T)`.
This is how wrapped laws on the circle obtain their densities.
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

section Periodization

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M]

omit hT in
-- `automorphize` is a `Quotient.lift`, so at a real point it is the orbit sum by definition.
private theorem automorphize_coe_eq_tsum_vadd (f : ℝ → M) (x : ℝ) :
    QuotientAddGroup.automorphize f (x : AddCircle T) =
      ∑' γ : (AddSubgroup.zmultiples T).op, f (γ +ᵥ x) :=
  rfl

/-- The periodization of a function on `ℝ`, evaluated at a real point, is the sum of the
function over the translates of that point by multiples of the period. -/
theorem automorphize_coe (f : ℝ → M) (x : ℝ) :
    QuotientAddGroup.automorphize f (x : AddCircle T) = ∑' k : ℤ, f (x + k • T) := by
  let e : ℤ ≃ (AddSubgroup.zmultiples T).op :=
    (AddSubgroup.zmultiplesEquivInt hT.out.ne').symm.toEquiv.trans (AddSubgroup.equivOp _)
  rw [automorphize_coe_eq_tsum_vadd, ← e.tsum_eq]
  refine tsum_congr fun k ↦ congrArg f ?_
  simp [e, AddSubgroup.vadd_def, AddSubgroup.coe_zmultiplesEquivInt_symm_apply]

/-- Reducing a real law with density `f` modulo `T` gives the circle law whose density
relative to circle volume is the periodization of `f`. -/
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
  · simp [indicator, hx, h, automorphize_coe_eq_tsum_vadd]
  · simp [indicator, hx, h]

end Periodization

end AddCircle
