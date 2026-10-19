/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support

/-!
# Topological support under homeomorphisms

This file shows that pushing a measure forward along a homeomorphism transports its topological
support onto the image of the original support.

## Main result

* `MeasureTheory.Measure.support_map_homeomorph` — the support of a pushforward by a
  homeomorphism is the image of the original support.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

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
