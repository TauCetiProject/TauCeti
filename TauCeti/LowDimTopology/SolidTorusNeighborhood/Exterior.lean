/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic

/-!
# Knot exteriors from solid-torus neighbourhoods

The exterior of a framed knot is the complement of the open solid torus in a solid-torus
neighbourhood. This file gives that complement a named carrier and records the compactness and
boundary facts needed by Dehn filling. The smooth manifold-with-boundary structure on this carrier
is a later construction; the boundary parametrization here is already the framed torus supplied by
the neighbourhood.

The definition and its elementary topological properties follow Rolfsen, *Knots and Links*,
Sections 2E and 9F.
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*}

/-- The closed exterior of a solid-torus neighbourhood: the complement of its open solid-torus
image. -/
def knotExterior {Φ : SolidTorus → X} : Set X :=
  (Φ '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1})ᶜ

/-- Membership in the exterior means that a point is outside the open solid-torus image. -/
@[simp]
theorem mem_knotExterior {Φ : SolidTorus → X} {x : X} :
    x ∈ knotExterior (Φ := Φ) ↔ x ∉ Φ '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} :=
  Iff.rfl

section Topology

variable [TopologicalSpace X]

/-- The exterior is closed in any ambient topological space. -/
theorem IsSolidTorusNeighborhood.isClosed_exterior
    {f : Circle → X} {Φ : SolidTorus → X} (h : IsSolidTorusNeighborhood f Φ) :
    IsClosed (knotExterior (Φ := Φ)) := by
  exact h.isOpen_image.isClosed_compl

/-- In a compact ambient space, the knot exterior is compact. -/
theorem IsSolidTorusNeighborhood.isCompact_exterior [CompactSpace X]
    {f : Circle → X} {Φ : SolidTorus → X} (h : IsSolidTorusNeighborhood f Φ) :
    IsCompact (knotExterior (Φ := Φ)) := by
  exact h.isClosed_exterior.isCompact

/-- The framed boundary torus is the frontier of the knot exterior. -/
theorem IsSolidTorusNeighborhood.exterior_frontier
    [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
    (h : IsSolidTorusNeighborhood f Φ) :
    frontier (knotExterior (Φ := Φ)) = range (Φ ∘ SolidTorus.boundaryInclusion) := by
  rw [knotExterior, frontier_compl]
  exact h.frontier_image


end Topology

end TauCeti
