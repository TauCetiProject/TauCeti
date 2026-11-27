/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.SubordinatePartition

/-!
# Checks for subordinate partitions

For a group acting trivially on the two points of `Bool`, every orbit is a point. The singleton
partition (label `id`) is subordinate to every subgroup, for every measure, while the constant
partition is subordinate at no point: its atom has two points and does not lie in an orbit.
-/

public section

open MeasureTheory Set

namespace TauCeti.Examples.SubordinatePartition

variable {G : Type*} [Group G] [TopologicalSpace G] [MulAction G Bool]

/-- Under a trivial action, the singleton partition is subordinate to `V` at every point. -/
theorem isSubordinateAt_id (htriv : ∀ (g : G) (b : Bool), g • b = b) (V : Subgroup G)
    (b : Bool) : IsSubordinateAt V id b := by
  refine isSubordinateAt_iff.2
    ⟨⟨{1}, isCompact_singleton, fun c hc ↦ ⟨1, rfl, by simpa using hc.symm⟩⟩,
    univ, isOpen_univ, mem_univ _, ?_⟩
  rintro _ ⟨v, -, rfl⟩
  simp [htriv]

/-- Under a trivial action, the singleton partition of `Bool` is subordinate to every subgroup for
every measure. -/
def singleton (htriv : ∀ (g : G) (b : Bool), g • b = b) (μ : Measure Bool) (V : Subgroup G) :
    TauCeti.SubordinatePartition G μ V Bool where
  label := id
  measurable_label := measurable_id
  ae_isSubordinateAt := Filter.Eventually.of_forall (isSubordinateAt_id htriv V)

/-- Under a trivial action, the constant partition of `Bool` is subordinate at no point: its atom
contains the other point, which is not in the orbit. -/
theorem not_isSubordinateAt_const (htriv : ∀ (g : G) (b : Bool), g • b = b) (V : Subgroup G)
    (b : Bool) : ¬ IsSubordinateAt V (fun _ : Bool ↦ ()) b := by
  rw [isSubordinateAt_iff]
  rintro ⟨⟨K, -, hK⟩, -⟩
  obtain ⟨v, -, hv⟩ := hK (mem_preimage.2 rfl : (!b) ∈ (fun _ : Bool ↦ ()) ⁻¹' {()})
  simp [htriv] at hv

end TauCeti.Examples.SubordinatePartition
