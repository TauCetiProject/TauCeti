/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Restricting a measure to its support

When the topological support is conull, pulling a measure back to it gives a measure positive
on every nonempty open set of that subtype, and the inclusion preserves the measure.
These facts allow measured spaces to discard points outside their support without changing
their measure. Supports also commute with pushforward by homeomorphisms.
-/

public section

open MeasureTheory Set Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- If the support is conull, the pullback measure is positive on nonempty relatively open
sets of the support. -/
theorem isOpenPosMeasure_comap_subtype_support (μ : Measure X)
    (hμ : μ.support ∈ ae μ) :
    (μ.comap ((↑) : μ.support → X)).IsOpenPosMeasure := by
  refine ⟨fun U hU ⟨x, hx⟩ ↦ ?_⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  rw [comap_subtype_coe_apply μ.isClosed_support.measurableSet]
  have himage : (Subtype.val '' (Subtype.val ⁻¹' V : Set μ.support)) = V ∩ μ.support := by
    simp [image_preimage_eq_inter_range]
  rw [himage]
  have hpos := (Measure.mem_support_iff_forall x.1).1 x.2 V (hV.mem_nhds hx)
  have heq : μ (V ∩ μ.support) = μ V := measure_congr (by
    filter_upwards [hμ] with y hy
    simp [hy])
  exact ne_of_gt (heq.symm ▸ hpos)

/-- A homeomorphism transports the support exactly, without a regularity hypothesis. -/
theorem support_map_homeomorph [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (e : X ≃ₜ Y) : (μ.map e).support = e '' μ.support := by
  ext y
  simp only [Measure.support_eq_forall_isOpen, mem_ofPred_eq]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro U hyU hU
    have hpos := hy (e '' U) ⟨e.symm y, hyU, e.apply_symm_apply y⟩ (e.isOpenMap U hU)
    simpa [Measure.map_apply e.measurable (e.isOpenMap U hU).measurableSet] using hpos
  · rintro ⟨x, hx, rfl⟩ U hxU hU
    rw [Measure.map_apply e.measurable hU.measurableSet]
    exact hx (e ⁻¹' U) hxU (hU.preimage e.continuous)

end TauCeti
