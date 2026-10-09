/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.JacobsonSpace

/-!
# Lifting closed points from the image of a Jacobson space

For a continuous map from a Jacobson space, every closed point in its image has a closed
lift. Indeed, its nonempty closed fiber contains a closed point by
`nonempty_inter_closedPoints`. This is the topological input for closed-point lifting
along morphisms locally of finite type into Jacobson schemes.
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
