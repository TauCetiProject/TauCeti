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

* `Homeomorph.isCoveringMap`: a homeomorphism is a covering map.
* `IsCoveringMap.id`: the identity of a space is a covering map.
-/

public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism is a covering map, with the whole base as an evenly covered neighbourhood. -/
theorem Homeomorph.isCoveringMap (e : X ≃ₜ Y) : IsCoveringMap e := by
  intro y
  have : Subsingleton (e ⁻¹' {y} : Set X) :=
    (Set.subsingleton_singleton.preimage e.injective).coe_sort
  exact ⟨inferInstance, .univ, trivial, isOpen_univ, isOpen_univ,
    { toFun x := (⟨e x, trivial⟩, ⟨e.symm y, by simp⟩)
      invFun u := ⟨e.symm u.1, trivial⟩
      left_inv x := Subtype.ext (e.symm_apply_apply x)
      right_inv u := Prod.ext (by simp) (Subsingleton.elim _ _) }, fun _ ↦ rfl⟩

/-- The identity of a space is a covering map, the trivial one-sheeted cover. -/
protected theorem IsCoveringMap.id : IsCoveringMap (@id X) :=
  (Homeomorph.refl X).isCoveringMap
