/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Homeomorphisms are covering maps

A homeomorphism is a covering map with one-point fibres: the whole base is evenly covered. In
particular the identity of a space is a covering map, the trivial one-sheeted cover.

## Main results

* `IsCoveringMap.id`: the identity of a space is a covering map.
* `IsHomeomorph.isCoveringMap`: a homeomorphism is a covering map.
* `Homeomorph.isCoveringMap`: the bundled form of the previous result.
-/

public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The identity of a space is a covering map, the trivial one-sheeted cover: the whole space is
an evenly covered neighbourhood of every point. -/
protected theorem IsCoveringMap.id : IsCoveringMap (@id X) := fun _ ↦
  IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Unit)
    ⟨inferInstance, .univ, trivial, isOpen_univ, isOpen_univ, (Homeomorph.prodPUnit _).symm,
      fun _ ↦ rfl⟩

/-- A homeomorphism is a covering map, with the whole base as an evenly covered neighbourhood. -/
theorem IsHomeomorph.isCoveringMap {f : X → Y} (hf : IsHomeomorph f) : IsCoveringMap f := by
  convert IsCoveringMap.id.homeomorph_comp (hf.homeomorph f) using 1
  ext
  simp

/-- A bundled homeomorphism is a covering map; see `IsHomeomorph.isCoveringMap`. -/
theorem Homeomorph.isCoveringMap (e : X ≃ₜ Y) : IsCoveringMap e := by
  simpa only [Function.comp_id] using IsCoveringMap.id.homeomorph_comp e
