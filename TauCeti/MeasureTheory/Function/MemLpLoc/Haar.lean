/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MemLpLoc.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar-measure independence and affine invariance of local `Lᵖ` classes

Scaling the ambient measure by a positive finite scalar preserves and reflects `Lᵖ` membership on
compact sets (`TauCeti.memLpLoc_smul_measure_iff`), so on a locally compact second-countable
topological additive group `TauCeti.MemLpLoc` is independent of the choice of additive Haar measure
(`TauCeti.memLpLoc_iff_of_isAddHaarMeasure`, `TauCeti.memLpLoc_congr_measureSpace`).

Consequently, right translations (`TauCeti.MemLpLoc.comp_add_right`,
`TauCeti.memLpLoc_comp_add_right_iff`), continuous linear equivalences
(`TauCeti.MemLpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memLpLoc_comp_iff`), and
real-affine equivalences (`TauCeti.MemLpLoc.comp_continuousLinearEquiv_add`) preserve local `Lᵖ`
classes between arbitrary Borel additive Haar measures.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

universe u u₁ v

section SmulMeasure

private theorem volume_mk {E : Type u} [MeasurableSpace E] (μ : Measure E) :
    @volume E ⟨μ⟩ = μ := rfl

/-- Scaling the ambient measure by a positive finite constant preserves and reflects local `Lᵖ`
membership. -/
theorem memLpLoc_smul_measure_iff {E : Type u} {F : Type v}
    [TopologicalSpace E] [MeasurableSpace E] [NormedAddCommGroup F]
    {μ : Measure E} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    {p : ENNReal} {U : Set E} {f : E → F} :
    @MemLpLoc E F _ ⟨c • μ⟩ _ p U f ↔ @MemLpLoc E F _ ⟨μ⟩ _ p U f := by
  refine ⟨fun h => (@memLpLoc_iff E F _ ⟨μ⟩ _ _ _ _).2 fun K hKU hK => ?_,
    fun h => (@memLpLoc_iff E F _ ⟨c • μ⟩ _ _ _ _).2 fun K hKU hK => ?_⟩
  · have h' := ((@memLpLoc_iff E F _ ⟨c • μ⟩ _ _ _ _).1 h K hKU hK).smul_measure
      (ENNReal.inv_ne_top.2 hc0)
    rwa [volume_mk, Measure.restrict_smul, smul_smul, ENNReal.inv_mul_cancel hc0 hc,
      one_smul] at h'
  · rw [volume_mk, Measure.restrict_smul]
    exact ((@memLpLoc_iff E F _ ⟨μ⟩ _ _ _ _).1 h K hKU hK).smul_measure hc

end SmulMeasure

section HaarIndependence

/-- Local `Lᵖ` membership on a locally compact second-countable topological additive group is
independent of the choice of additive Haar measure. -/
theorem memLpLoc_iff_of_isAddHaarMeasure {E : Type u} {F : Type v}
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] {μ ν : Measure E} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ENNReal} {U : Set E} {f : E → F} :
    @MemLpLoc E F _ ⟨μ⟩ _ p U f ↔ @MemLpLoc E F _ ⟨ν⟩ _ p U f := by
  rw [Measure.isAddLeftInvariant_eq_smul μ ν, ← Measure.coe_nnreal_smul]
  exact memLpLoc_smul_measure_iff
    (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne')
    ENNReal.coe_ne_top

/-- Local `Lᵖ` membership is independent of the `MeasureSpace` instance among Borel additive Haar
measures. -/
theorem memLpLoc_congr_measureSpace {E : Type u} {F : Type v}
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] [SecondCountableTopology E] [NormedAddCommGroup F]
    (m₁ m₂ : MeasureSpace E)
    [hB₁ : @BorelSpace E _ m₁.toMeasurableSpace]
    [hB₂ : @BorelSpace E _ m₂.toMeasurableSpace]
    [@Measure.IsAddHaarMeasure E _ _ m₁.toMeasurableSpace m₁.volume]
    [@Measure.IsAddHaarMeasure E _ _ m₂.toMeasurableSpace m₂.volume]
    {p : ENNReal} {U : Set E} {f : E → F} :
    @MemLpLoc E F _ m₁ _ p U f ↔ @MemLpLoc E F _ m₂ _ p U f := by
  rcases m₁ with @⟨m₁, μ⟩
  rcases m₂ with @⟨m₂, ν⟩
  have hm : m₁ = m₂ := hB₁.measurable_eq.trans hB₂.measurable_eq.symm
  subst hm
  exact memLpLoc_iff_of_isAddHaarMeasure

end HaarIndependence

section Translation

/-- Right translation preserves local `Lᵖ` membership under any right-invariant Borel measure. -/
theorem MemLpLoc.comp_add_right {E : Type u} {F : Type v}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddRightInvariant]
    [NormedAddCommGroup F] {p : ENNReal} {U V : Set E} {u : E → F}
    (hu : MemLpLoc p V u) (b : E) (hmaps : MapsTo (· + b) U V) :
    MemLpLoc p U (fun x => u (x + b)) := by
  have hcont : Continuous (· + b) := continuous_id.add continuous_const
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hu' : MemLp u p (volume.restrict ((· + b) '' K)) :=
    memLpLoc_iff.1 hu _ ((image_mono hKU).trans hmaps.image_subset) (hK.image hcont)
  exact hu'.comp_measurePreserving
    ((measurePreserving_add_right (volume : Measure E) b).restrict_image_emb
      (measurableEmbedding_addRight b) K)

/-- Right translation preserves and reflects local `Lᵖ` membership. -/
@[simp]
theorem memLpLoc_comp_add_right_iff {E : Type u} {F : Type v}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddRightInvariant]
    [NormedAddCommGroup F] {p : ENNReal} {V : Set E} {u : E → F} (b : E) :
    MemLpLoc p ((· + b) ⁻¹' V) (fun x => u (x + b)) ↔ MemLpLoc p V u := by
  refine ⟨fun h => ?_, fun h => h.comp_add_right b (mapsTo_preimage (· + b) V)⟩
  simpa only [add_assoc, neg_add_cancel, add_zero] using
    h.comp_add_right (-b) fun x hx => by
      simpa [mem_preimage, add_assoc, neg_add_cancel, add_zero] using hx

end Translation

section LinearAndAffineLp

variable {E : Type u} {E₁ : Type u₁} {F : Type v}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [LocallyCompactSpace E₁] [SecondCountableTopology E₁]
  [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
  [NormedAddCommGroup F]

/-- Precomposition with a continuous linear equivalence between spaces carrying arbitrary Borel
additive Haar measures preserves local `Lᵖ` membership. -/
theorem MemLpLoc.comp_continuousLinearEquiv {p : ENNReal} {U : Set E} {V : Set E₁}
    {u : E₁ → F} (hu : MemLpLoc p V u) (e : E ≃L[ℝ] E₁) (hmaps : MapsTo e U V) :
    MemLpLoc p U (u ∘ e) := by
  have : ((volume : Measure E).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hu' : @MemLpLoc E₁ F _ ⟨(volume : Measure E).map e⟩ _ p V u :=
    (memLpLoc_iff_of_isAddHaarMeasure (μ := (volume : Measure E).map e) (ν := volume)).2 hu
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hmem : MemLp u p (((volume : Measure E).map e).restrict (e '' K)) :=
    (@memLpLoc_iff E₁ F _ ⟨(volume : Measure E).map e⟩ _ _ _ _).1 hu' _
      ((image_mono hKU).trans hmaps.image_subset) (hK.image e.continuous)
  have he : MeasurePreserving e (volume : Measure E) ((volume : Measure E).map e) :=
    ⟨e.continuous.measurable, rfl⟩
  exact hmem.comp_measurePreserving (he.restrict_image_emb e.toHomeomorph.measurableEmbedding K)

/-- Precomposition with a continuous linear equivalence preserves and reflects local `Lᵖ`
membership. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff [LocallyCompactSpace E]
    [SecondCountableTopology E] {p : ENNReal} {V : Set E₁} {u : E₁ → F}
    (e : E ≃L[ℝ] E₁) :
    MemLpLoc p (e ⁻¹' V) (u ∘ e) ↔ MemLpLoc p V u := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  simpa [Function.comp_def] using
    h.comp_continuousLinearEquiv e.symm fun y hy => by simpa [mem_preimage] using hy

/-- Real-affine changes of variables between spaces carrying arbitrary Borel additive Haar measures
preserve local `Lᵖ` membership. -/
theorem MemLpLoc.comp_continuousLinearEquiv_add {p : ENNReal} {U : Set E} {V : Set E₁}
    {u : E₁ → F} (hu : MemLpLoc p V u) (A : E ≃L[ℝ] E₁) (b : E₁)
    (hmaps : MapsTo (fun x => A x + b) U V) :
    MemLpLoc p U (fun x => u (A x + b)) :=
  (hu.comp_add_right b (mapsTo_preimage (· + b) V)).comp_continuousLinearEquiv A hmaps

end LinearAndAffineLp

end TauCeti
