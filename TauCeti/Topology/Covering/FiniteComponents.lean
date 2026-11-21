/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Topology.Connected.CardComponents
public import TauCeti.Topology.Covering.IsFiniteCover
public import TauCeti.Topology.Covering.Proper

/-!
# Components of finite covers of connected spaces

A finite cover of a connected space has finitely many connected components. The finiteness
follows from the open and proper map properties and a finite fibre.
-/

public section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A finite cover of a connected space has finitely many connected components. -/
theorem IsFiniteCover.finite_connectedComponents [ConnectedSpace Y]
    {p : X → Y} (hp : IsFiniteCover p) :
    Finite (ConnectedComponents X) := by
  classical
  rcases isEmpty_or_nonempty Y with h | h
  · let : IsEmpty X := ⟨fun x ↦ isEmptyElim (p x)⟩
    exact Finite.of_surjective _ ConnectedComponents.surjective_coe
  · let := h
    exact hp.isCoveringMap.isOpenMap
      |>.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
        (hp.isCoveringMap.isProperMap hp.finite_fiber).isClosedMap
        (Set.finite_coe_iff.mp (hp.finite_fiber (Classical.choice h)))

end TauCeti
