/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Connected.PathConnected

/-!
# Rings with open units: the inverse and path-connectedness

A topological monoid `M` has open units (`IsOpenUnits M`) when `Units.val : Mˣ → M` is an open
embedding: the units are open and inversion is continuous on them for the subspace topology.
In a monoid with zero with open units, `Ring.inverse` is therefore continuous at every unit.
Whenever `Units.val : Mˣ → M` is a topological embedding onto `{m : M | IsUnit m}`, the set of
units is path-connected if and only if the topological group `Mˣ` is.

## Main declarations

* `IsOpenUnits.continuousAt_ringInverse`: `Ring.inverse` is continuous at every unit of a ring
  with open units.
* `Topology.IsEmbedding.isPathConnected_isUnit_iff`: when `Units.val : Mˣ → M` is an embedding,
  `{m : M | IsUnit m}` is path-connected if and only if `Mˣ` is.
-/

public section

open Topology

variable {R : Type*} [MonoidWithZero R] [TopologicalSpace R] [IsOpenUnits R]

/-- In a monoid with zero whose units are open with continuous inversion, `Ring.inverse` is
continuous at every unit. -/
theorem IsOpenUnits.continuousAt_ringInverse (u : Rˣ) : ContinuousAt Ring.inverse (u : R) := by
  rw [← IsOpenUnits.isOpenEmbedding_unitsVal.continuousAt_iff]
  have : (Ring.inverse ∘ Units.val : Rˣ → R) = fun v ↦ ↑v⁻¹ := by
    funext v
    exact Ring.inverse_unit v
  rw [this]
  exact Units.continuous_coe_inv.continuousAt

namespace Topology

/-- In a topological monoid `M` whose unit inclusion `Units.val : Mˣ → M` is an embedding (for
example, a normed ring with summable geometric series or a topological monoid with open units), the
set `{m : M | IsUnit m}` of invertible elements is path-connected if and only if the topological
group `Mˣ` is path-connected. -/
theorem IsEmbedding.isPathConnected_isUnit_iff {M : Type*} [Monoid M] [TopologicalSpace M]
    (h : IsEmbedding (Units.val : Mˣ → M)) :
    IsPathConnected {m : M | IsUnit m} ↔ PathConnectedSpace Mˣ := by
  have hrange : (Units.val : Mˣ → M) '' Set.univ = {m : M | IsUnit m} := by
    ext m
    exact ⟨fun ⟨u, _, hu⟩ ↦ hu ▸ u.isUnit, fun hm ↦ ⟨hm.unit, Set.mem_univ _, hm.unit_spec⟩⟩
  rw [← hrange, ← h.isInducing.isPathConnected_iff, pathConnectedSpace_iff_univ]

end Topology
