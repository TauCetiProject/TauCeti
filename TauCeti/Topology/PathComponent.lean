/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import TauCeti.Topology.Homotopy.Path

/-!
# Point-set topology of path components

Paths and path homotopies based in `pathComponent x₀` remain in that component, without any
local path-connectedness assumption. This gives path connectedness of the component as a
subspace; under local path connectedness of the ambient space, openness of path components also
gives local path connectedness of the subspace.

## Main declarations

* `TauCeti.homotopic_pathComponent_of_map_subtypeVal_homotopic`: path homotopies reflect along
  the inclusion of a path component.
* Instances making `↥(pathComponent x₀)` path connected and locally path connected.
* `TauCeti.pathComponentSelf`: a point viewed in its own path component.
* `Joined.eq_of_totallyDisconnectedSpace` and
  `ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace`: in a totally disconnected space,
  the path components are the points.
* `TauCeti.PathComponentBasepoints`: a choice of a basepoint in each path component.

## References

This supplies point-set prerequisites for the "or one builds the cover of `pathComponent x₀`"
clause in `TauCetiRoadmap/UniversalCovers/README.md`.
-/

public section

open scoped unitInterval
open Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- Two paths in a path component which are homotopic in the ambient space are already
homotopic in the path component. -/
theorem homotopic_pathComponent_of_map_subtypeVal_homotopic
    {a b : pathComponent x₀} {γ δ : Path a b}
    (h : (γ.map continuous_subtype_val).Homotopic
      (δ.map continuous_subtype_val)) :
    γ.Homotopic δ := by
  obtain ⟨H⟩ := h
  have hγmem : ∀ t, (γ.map continuous_subtype_val) t ∈ pathComponent x₀ := fun t =>
    (γ t).2
  have hmem : ∀ p : I × I, H p ∈ pathComponent x₀ := fun p =>
    Joined.mem_pathComponent
      ((H.evalAt p.2).mem_pathComponent p.1)
      (H.map_zero_left p.2 ▸ hγmem p.2)
  exact Path.homotopic_of_continuous_square (fun p => ⟨H p, hmem p⟩)
    (H.continuous.subtype_mk hmem) (fun t => Subtype.ext (H.map_zero_left t))
    (fun t => Subtype.ext (H.map_one_left t)) (fun t => Subtype.ext (H.source t))
    (fun t => Subtype.ext (H.target t))

/-- The path component of a point, as a subspace, is path connected. -/
instance instPathConnectedSpaceSubtypePathComponent :
    PathConnectedSpace (pathComponent x₀) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

/-- In a locally path connected space the path components are open, hence locally path connected
as subspaces. -/
instance instLocallyPathConnectedSpaceSubtypePathComponent [LocallyPathConnectedSpace X] :
    LocallyPathConnectedSpace (pathComponent x₀) :=
  (IsOpen.pathComponent x₀).locallyPathConnectedSpace

/-- The basepoint of `X`, viewed as a point of its own path component. -/
abbrev pathComponentSelf : (pathComponent x₀ : Set X) :=
  ⟨x₀, mem_pathComponent_self x₀⟩

/-- In a totally disconnected space, points joined by a path are equal. -/
theorem _root_.Joined.eq_of_totallyDisconnectedSpace [TotallyDisconnectedSpace X] {x y : X}
    (h : Joined x y) : x = y := by
  obtain ⟨γ⟩ := h
  simpa using (isPreconnected_range γ.continuous).subsingleton
    (Set.mem_range_self 0) (Set.mem_range_self 1)

/-- In a totally disconnected space, distinct points lie in distinct path components. -/
theorem _root_.ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace
    [TotallyDisconnectedSpace X] : Function.Injective (ZerothHomotopy.mk (X := X)) :=
  fun _ _ h ↦ Joined.eq_of_totallyDisconnectedSpace (Quotient.exact h)

/-- A choice of a basepoint in each path component of a space: a section of the projection
`ZerothHomotopy.mk` to the set of path components. -/
structure PathComponentBasepoints (X : Type*) [TopologicalSpace X] where
  /-- The chosen basepoint of a path component. -/
  point : ZerothHomotopy X → X
  /-- The chosen basepoint of a path component lies in that component. -/
  mk_point : ∀ c, ZerothHomotopy.mk (point c) = c

end TauCeti
