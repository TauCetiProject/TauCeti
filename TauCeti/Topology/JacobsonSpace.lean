/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.JacobsonSpace

/-!
# Closed points of Jacobson spaces

For a continuous map from a Jacobson space, every closed point in its image has a closed
lift. Indeed, its nonempty closed fiber contains a closed point by
`nonempty_inter_closedPoints`. This is the topological input for closed-point lifting
along morphisms locally of finite type into Jacobson schemes.

A closed subset of a Jacobson space with only finitely many closed points is finite, since it is
the closure of its closed points. For a scheme locally of finite type over a field, this reduces
the finiteness of a closed subset, such as a fibre of a morphism, to counting its closed points.
-/

public section

namespace Continuous

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [JacobsonSpace X]
  {f : X → Y}

/-- Every closed point in the image of a continuous map from a Jacobson space has a closed
lift. -/
theorem exists_isClosed_singleton_of_mem_range (hf : Continuous f) {y : Y}
    (hy : IsClosed {y}) (hyf : y ∈ Set.range f) :
    ∃ x : X, IsClosed {x} ∧ f x = y := by
  obtain ⟨x, hx⟩ := hyf
  have hne : (f ⁻¹' {y}).Nonempty := ⟨x, hx⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hne
    (hy.preimage hf).isLocallyClosed
  exact ⟨z, hzc, hz⟩

end Continuous

/-- **A closed subset of a Jacobson space with finitely many closed points is finite**: it is the
closure of its closed points, and a finite set of closed points is closed. -/
theorem IsClosed.finite_of_finite_inter_closedPoints {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {Z : Set X} (hZ : IsClosed Z) (h : (Z ∩ closedPoints X).Finite) :
    Z.Finite := by
  have hc : IsClosed (Z ∩ closedPoints X) := by
    rw [← (Z ∩ closedPoints X).biUnion_of_singleton]
    exact h.isClosed_biUnion fun _ hx ↦ hx.2
  rwa [← closure_inter_closedPoints hZ, hc.closure_eq]
