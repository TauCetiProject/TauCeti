/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support

/-!
# Topological support under continuous maps

This file identifies the support of a pushforward by a continuous map as the closure of the
image of the source support. It also shows that pushing a measure forward along a homeomorphism
transports its topological support onto the image of the original support.

## Main result

* `MeasureTheory.Measure.support_map_eq_closure_image` — a continuous pushforward has support
  equal to the closure of the image of the support, when the source support has full measure.
* `MeasureTheory.Measure.support_map_eq_closure_range` — a continuous image of a full-support
  measure has support equal to the closure of the map's range.
* `MeasureTheory.Measure.support_map_homeomorph` — the support of a pushforward by a homeomorphism
  is the image of the original support.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The support of a continuous pushforward is the closure of the image of the support,
provided that the source support has full measure. -/
theorem support_map_eq_closure_image (μ : Measure X) (hμ : μ.support ∈ ae μ)
    {f : X → Y} (hf : Continuous f) :
    (μ.map f).support = closure (f '' μ.support) := by
  apply Set.Subset.antisymm
  · apply support_subset_of_isClosed isClosed_closure
    exact (ae_map_iff hf.measurable.aemeasurable isClosed_closure.measurableSet).2 <|
      (Filter.eventually_mem_set.mpr hμ).mono fun x hx ↦ subset_closure (mem_image_of_mem f hx)
  · refine closure_minimal ?_ isClosed_support
    rintro _ ⟨x, hx, rfl⟩
    rw [support_eq_forall_isOpen]
    intro U hxU hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    exact (mem_support_iff_forall x).mp hx (f ⁻¹' U)
      ((hU.preimage hf).mem_nhds hxU)

/-- The support of the pushforward of a full-support measure by a continuous map is the closure of
the map's range. No injectivity, surjectivity, or properness hypothesis is needed. -/
theorem support_map_eq_closure_range (μ : Measure X) {f : X → Y} (hμ : μ.support = Set.univ)
    (hf : Continuous f) : (μ.map f).support = closure (Set.range f) := by
  rw [support_map_eq_closure_image μ (by simp [hμ]) hf, hμ, image_univ]

/-- A homeomorphism carries the support of a measure onto the support of its pushforward. -/
theorem support_map_homeomorph (μ : Measure X) (e : X ≃ₜ Y) :
    (μ.map e).support = e '' μ.support := by
  ext y
  rw [Measure.support_eq_forall_isOpen, e.image_eq_preimage_symm, Set.mem_preimage,
    Measure.support_eq_forall_isOpen]
  constructor
  · intro hy U hyU hU
    have hey : y ∈ e '' U := ⟨e.symm y, hyU, e.apply_symm_apply y⟩
    have heU : IsOpen (e '' U) := e.isOpenMap U hU
    have hpos := hy (e '' U) hey heU
    rw [Measure.map_apply e.measurable heU.measurableSet, e.preimage_image] at hpos
    exact hpos
  · intro hx U hyU hU
    rw [Measure.map_apply e.measurable hU.measurableSet]
    exact hx (e ⁻¹' U) (by simpa) (hU.preimage e.continuous)

end MeasureTheory.Measure
