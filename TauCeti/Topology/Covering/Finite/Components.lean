/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Topology.Connected.CardComponents
public import TauCeti.Topology.Covering.Proper

/-!
# Components of finite covers of connected spaces

A covering map with finite fibres over a preconnected space has finitely many connected
components in its total space. Thus a finite cover splits into only finitely many connected
covering spaces, even without compactness assumptions.
-/

public section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A covering map with finite fibres over a preconnected space has finitely many connected
components in its total space. -/
theorem _root_.IsCoveringMap.finite_connectedComponents [PreconnectedSpace Y]
    {p : X → Y} (hp : IsCoveringMap p) (hfin : ∀ y, Finite (p ⁻¹' {y})) :
    Finite (ConnectedComponents X) := by
  classical
  rcases isEmpty_or_nonempty Y with h | h
  · let : IsEmpty X := ⟨fun x ↦ isEmptyElim (p x)⟩
    exact Finite.of_surjective _ ConnectedComponents.surjective_coe
  · let : ConnectedSpace Y := ⟨h⟩
    exact hp.isOpenMap
      |>.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
        (hp.isProperMap hfin).isClosedMap
        (Set.finite_coe_iff.mp (hfin (Classical.choice h)))

end TauCeti
