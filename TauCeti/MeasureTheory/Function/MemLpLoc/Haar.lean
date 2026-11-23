/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MemLpLoc
import Mathlib.MeasureTheory.Group.Measure

/-!
# Measure scaling, translation, and affine invariance of local `Lᵖ` classes

Scaling the ambient measure by a positive finite scalar preserves and reflects `Lᵖ` membership on
compact sets (`TauCeti.memLpLoc_smul_measure_iff`). Combined with Haar-measure independence
(`TauCeti.memLpLoc_iff_of_isAddHaarMeasure`) and linear invariance
(`ContinuousLinearEquiv.memLpLoc_comp_right_iff`) from `TauCeti.MeasureTheory.Function.MemLpLoc`,
right translations (`TauCeti.MemLpLoc.comp_add_right`, `TauCeti.memLpLoc_comp_add_right_iff`),
continuous linear equivalences (`TauCeti.MemLpLoc.comp_continuousLinearEquiv`), and real-affine
equivalences (`TauCeti.MemLpLoc.comp_continuousLinearEquiv_add`) preserve local `Lᵖ` classes
between arbitrary Borel additive Haar measures.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

section SmulMeasure

/-- Scaling the ambient measure by a positive finite constant preserves and reflects local `Lᵖ`
membership. -/
theorem memLpLoc_smul_measure_iff {X F : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup F]
    {μ : Measure X} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    {p : ENNReal} {U : Set X} {f : X → F} :
    MemLpLoc p U f (c • μ) ↔ MemLpLoc p U f μ := by
  refine ⟨fun h => memLpLoc_iff.2 fun K hKU hK => ?_,
    fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  · have h' := (memLpLoc_iff.1 h K hKU hK).smul_measure (ENNReal.inv_ne_top.2 hc0)
    rwa [Measure.restrict_smul, smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at h'
  · rw [Measure.restrict_smul]
    exact (memLpLoc_iff.1 h K hKU hK).smul_measure hc

end SmulMeasure

section Translation

/-- Right translation preserves local `Lᵖ` membership under any right-invariant Borel measure. -/
theorem MemLpLoc.comp_add_right {G F : Type*}
    [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddRightInvariant]
    [NormedAddCommGroup F] {p : ENNReal} {U V : Set G} {u : G → F}
    (hu : MemLpLoc p V u μ) (b : G) (hmaps : MapsTo (· + b) U V) :
    MemLpLoc p U (fun x => u (x + b)) μ := by
  have hcont : Continuous (· + b) := continuous_id.add continuous_const
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hu' : MemLp u p (μ.restrict ((· + b) '' K)) :=
    memLpLoc_iff.1 hu _ ((image_mono hKU).trans hmaps.image_subset) (hK.image hcont)
  exact hu'.comp_measurePreserving
    ((measurePreserving_add_right μ b).restrict_image_emb
      (measurableEmbedding_addRight b) K)

/-- Right translation preserves and reflects local `Lᵖ` membership. -/
@[simp]
theorem memLpLoc_comp_add_right_iff {G F : Type*}
    [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddRightInvariant]
    [NormedAddCommGroup F] {p : ENNReal} {V : Set G} {u : G → F} (b : G) :
    MemLpLoc p ((· + b) ⁻¹' V) (fun x => u (x + b)) μ ↔ MemLpLoc p V u μ := by
  refine ⟨fun h => ?_, fun h => h.comp_add_right b (mapsTo_preimage (· + b) V)⟩
  simpa only [add_assoc, neg_add_cancel, add_zero] using
    h.comp_add_right (-b) fun x hx => by
      simpa [mem_preimage, add_assoc, neg_add_cancel, add_zero] using hx

end Translation

section LinearAndAffineLp

variable {E E₁ F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedAddCommGroup F]

/-- Precomposition with a continuous linear equivalence onto a finite-dimensional real normed space
preserves local `Lᵖ` membership between arbitrary Borel additive Haar measures. -/
theorem MemLpLoc.comp_continuousLinearEquiv {μ : Measure E} [μ.IsAddHaarMeasure]
    {ν : Measure E₁} [ν.IsAddHaarMeasure] {p : ENNReal} {U : Set E} {V : Set E₁}
    {u : E₁ → F} (hu : MemLpLoc p V u ν) (e : E ≃L[ℝ] E₁) (hmaps : MapsTo e U V) :
    MemLpLoc p U (u ∘ e) μ :=
  ((e.memLpLoc_comp_right_iff μ ν).2 hu).mono_set hmaps.subset_preimage

/-- Real-affine changes of variables onto a finite-dimensional real normed space preserve local `Lᵖ`
membership between arbitrary Borel additive Haar measures. -/
theorem MemLpLoc.comp_continuousLinearEquiv_add {μ : Measure E} [μ.IsAddHaarMeasure]
    {ν : Measure E₁} [ν.IsAddHaarMeasure] {p : ENNReal} {U : Set E} {V : Set E₁}
    {u : E₁ → F} (hu : MemLpLoc p V u ν) (A : E ≃L[ℝ] E₁) (b : E₁)
    (hmaps : MapsTo (fun x => A x + b) U V) :
    MemLpLoc p U (fun x => u (A x + b)) μ :=
  (hu.comp_add_right b (mapsTo_preimage (· + b) V)).comp_continuousLinearEquiv A hmaps

end LinearAndAffineLp

end TauCeti
