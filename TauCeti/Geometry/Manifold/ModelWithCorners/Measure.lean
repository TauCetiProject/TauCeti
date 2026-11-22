/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Measure.Subtype
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Additive Haar measures on relatively open subsets of model ranges

Pulling an additive Haar measure on a real normed space `E` back to a relatively open subset
`I.symm ⁻¹' U ∩ Set.range I` of the range of a `ModelWithCorners ℝ E H` yields a measure positive
on nonempty relatively open subsets (`ModelWithCorners.isOpenPosMeasure_comap_range_inter`).
Consequently, on a finite-dimensional model space, two continuous nonnegative real densities
presenting the same weighted Haar measure on `I.symm ⁻¹' U ∩ Set.range I` agree pointwise there
(`ModelWithCorners.eqOn_of_withDensity_ofReal_eq`).

## Main results

* `ModelWithCorners.isOpenPosMeasure_comap_range_inter`: pulling an additive Haar measure back to
  a relatively open subset of `Set.range I` yields an open-positive measure.
* `ModelWithCorners.eqOn_of_withDensity_ofReal_eq`: continuous nonnegative real densities presenting
  the same weighted Haar measure on a relatively open subset of `Set.range I` agree pointwise there.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- Pulling an additive Haar measure back to a relatively open subset of `range I` yields a
measure positive on nonempty relatively open subsets. -/
theorem isOpenPosMeasure_comap_range_inter (I : ModelWithCorners ℝ E H)
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    {U : Set H} (hU : IsOpen U) :
    (ν.comap (Subtype.val : (I.symm ⁻¹' U ∩ range I : Set E) → E)).IsOpenPosMeasure := by
  set V : Set E := I.symm ⁻¹' U ∩ range I
  have hV : MeasurableSet V :=
    (hU.preimage I.continuous_symm).measurableSet.inter I.isClosed_range.measurableSet
  refine ⟨fun W hW ⟨⟨y, hyV⟩, hyW⟩ ↦ ?_⟩
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.1 hW
  have hyO : y ∈ O := by simpa [← hOW] using hyW
  have hO' : IsOpen (O ∩ I.symm ⁻¹' U) := hO.inter (hU.preimage I.continuous_symm)
  obtain ⟨z, hz⟩ := mem_closure_iff_nhds.1 (I.range_subset_closure_interior hyV.2)
    (O ∩ I.symm ⁻¹' U) (hO'.mem_nhds ⟨hyO, hyV.1⟩)
  have hopen : IsOpen ((O ∩ I.symm ⁻¹' U) ∩ interior (range I)) := hO'.inter isOpen_interior
  have hsub : (O ∩ I.symm ⁻¹' U) ∩ interior (range I) ⊆ Subtype.val '' W := by
    rintro w ⟨⟨hwO, hwU⟩, hwI⟩
    exact ⟨⟨w, ⟨hwU, interior_subset hwI⟩⟩, by simpa [← hOW] using hwO, rfl⟩
  rw [(MeasurableEmbedding.subtypeVal hV).comap_apply]
  exact ((hopen.measure_pos ν ⟨z, hz⟩).trans_le (measure_mono hsub)).ne'

/-- Continuous nonnegative real densities presenting the same weighted Haar measure on a
relatively open subset of `range I` agree pointwise there. -/
theorem eqOn_of_withDensity_ofReal_eq (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [ν.IsAddHaarMeasure]
    {U : Set H} (hU : IsOpen U) {w₁ w₂ : E → ℝ}
    (hw₁ : ContinuousOn w₁ (I.symm ⁻¹' U ∩ range I))
    (hw₂ : ContinuousOn w₂ (I.symm ⁻¹' U ∩ range I))
    (h1 : ∀ y ∈ I.symm ⁻¹' U ∩ range I, 0 ≤ w₁ y)
    (h2 : ∀ y ∈ I.symm ⁻¹' U ∩ range I, 0 ≤ w₂ y)
    (heq : (ν.restrict (I.symm ⁻¹' U ∩ range I)).withDensity (fun y ↦ ENNReal.ofReal (w₁ y)) =
      (ν.restrict (I.symm ⁻¹' U ∩ range I)).withDensity (fun y ↦ ENNReal.ofReal (w₂ y))) :
    EqOn w₁ w₂ (I.symm ⁻¹' U ∩ range I) := by
  set V : Set E := I.symm ⁻¹' U ∩ range I
  have hV : MeasurableSet V :=
    (hU.preimage I.continuous_symm).measurableSet.inter I.isClosed_range.measurableSet
  have hval : MeasurableEmbedding (Subtype.val : V → E) := .subtypeVal hV
  have : (ν.comap (Subtype.val : V → E)).IsOpenPosMeasure :=
    I.isOpenPosMeasure_comap_range_inter ν hU
  have hcomap (w : E → ℝ) :
      ((ν.restrict V).withDensity (fun y ↦ ENNReal.ofReal (w y))).comap (Subtype.val : V → E) =
        (ν.comap (Subtype.val : V → E)).withDensity fun y ↦ ENNReal.ofReal (w y.val) := by
    ext A hA
    rw [hval.comap_apply, withDensity_apply _ (hval.measurableSet_image' hA),
      withDensity_apply _ hA, Measure.restrict_restrict (hval.measurableSet_image' hA),
      inter_eq_left.2 (Subtype.coe_image_subset V A),
      hval.restrict_comap, ← hval.lintegral_map (fun y ↦ ENNReal.ofReal (w y)), hval.map_comap,
      Subtype.range_coe, Measure.restrict_restrict hV,
      inter_eq_right.2 (Subtype.coe_image_subset V A)]
  have hsubEq :
      (ν.comap (Subtype.val : V → E)).withDensity (fun y ↦ ENNReal.ofReal (w₁ y.val)) =
        (ν.comap (Subtype.val : V → E)).withDensity fun y ↦ ENNReal.ofReal (w₂ y.val) := by
    rw [← hcomap w₁, ← hcomap w₂, heq]
  have hfun := MeasureTheory.continuous_eq_of_withDensity_ofReal_eq
    (continuousOn_iff_continuous_domRestrict.1 hw₁)
    (continuousOn_iff_continuous_domRestrict.1 hw₂)
    (fun y ↦ h1 y.val y.property) (fun y ↦ h2 y.val y.property) hsubEq
  exact fun y hy ↦ congrFun hfun ⟨y, hy⟩

end ModelWithCorners
