/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Pulling a measure back to its support

Pullback along the inclusion of a measurable conull set preserves the measure. When the
topological support is conull, its pullback measure is positive on every nonempty open set
of the support subtype. Supports also commute with pushforward by homeomorphisms.

For a measure `μ` and a homeomorphism `e`, use `TauCeti.support_map_homeomorph μ e he`,
where `he : Measurable e`, to identify the support of the pushforward.
-/

public section

open MeasureTheory Set Topology

namespace TauCeti

/-- Pullback to a measurable conull set preserves the original measure under inclusion. -/
theorem measurePreserving_subtype_coe_of_ae_mem {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {s : Set X} (hs : MeasurableSet s) (hμ : ∀ᵐ x ∂μ, x ∈ s) :
    MeasurePreserving ((↑) : s → X) (μ.comap (↑)) μ := by
  simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using
    (measurePreserving_subtype_coe (μa := μ) hs)

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- If the support is conull, the pullback measure is positive on nonempty relatively open
sets of the support. -/
theorem isOpenPosMeasure_comap_subtype_support (μ : Measure X)
    (hs : MeasurableSet μ.support) (hμ : μ.support ∈ ae μ) :
    (μ.comap ((↑) : μ.support → X)).IsOpenPosMeasure := by
  refine ⟨fun U hU ⟨x, hx⟩ ↦ ?_⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  rw [comap_subtype_coe_apply hs]
  have himage : (Subtype.val '' (Subtype.val ⁻¹' V : Set μ.support)) = V ∩ μ.support := by
    simp [image_preimage_eq_inter_range]
  rw [himage]
  have hpos := (Measure.mem_support_iff_forall x.1).1 x.2 V (hV.mem_nhds hx)
  have heq : μ (V ∩ μ.support) = μ V := measure_congr (by
    filter_upwards [hμ] with y hy
    simp [hy])
  exact ne_of_gt (heq.symm ▸ hpos)

/-- A measurable homeomorphism transports the support exactly when target open sets are
measurable, without a regularity hypothesis. -/
theorem support_map_homeomorph
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure X) (e : X ≃ₜ Y) (he : Measurable e) :
    (μ.map e).support = e '' μ.support := by
  ext y
  simp only [Measure.support_eq_forall_isOpen, mem_ofPred_eq]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro U hyU hU
    have hpos := hy (e '' U) ⟨e.symm y, hyU, e.apply_symm_apply y⟩ (e.isOpenMap U hU)
    simpa [Measure.map_apply he (e.isOpenMap U hU).measurableSet] using hpos
  · rintro ⟨x, hx, rfl⟩ U hxU hU
    rw [Measure.map_apply he hU.measurableSet]
    exact hx (e ⁻¹' U) hxU (hU.preimage e.continuous)

end TauCeti
