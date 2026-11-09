/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.StructureGroupoid

/-!
# Membership in an intersection of structure groupoids

Mathlib defines the infimum `G ⊓ G'` of two structure groupoids as the groupoid whose members are
the open partial homeomorphisms belonging to both. `StructureGroupoid.mem_inf` records this as a
simp lemma, so that groupoids defined as an intersection, such as a smooth groupoid cut down by an
extra condition, can be opened without unfolding the definition.
-/

public section

variable {H : Type*} [TopologicalSpace H]

/-- An open partial homeomorphism belongs to `G ⊓ G'` exactly when it belongs to both groupoids. -/
@[simp]
theorem StructureGroupoid.mem_inf {G G' : StructureGroupoid H} {e : OpenPartialHomeomorph H H} :
    e ∈ G ⊓ G' ↔ e ∈ G ∧ e ∈ G' :=
  Iff.rfl
