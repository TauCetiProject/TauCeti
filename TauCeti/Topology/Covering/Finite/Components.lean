/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Topology.Connected.CardComponents
public import TauCeti.Topology.Covering.Proper

/-!
# Components of finite covers

A covering map with finite fibres over a space with finitely many connected components has
finitely many connected components in its total space. Thus a finite cover splits into only
finitely many connected covering spaces, even without compactness assumptions.
-/

public section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A covering map with finite fibres over a space with finitely many connected components has
finitely many connected components in its total space. -/
theorem _root_.IsCoveringMap.finite_connectedComponents [Finite (ConnectedComponents Y)]
    {p : X → Y} (hp : IsCoveringMap p) (hfin : ∀ y, Finite (p ⁻¹' {y})) :
    Finite (ConnectedComponents X) := by
  exact hp.isOpenMap.finite_connectedComponents_of_finite_preimage_singleton
    (hp.isProperMap hfin).isClosedMap hp.continuous
    (fun y ↦ Set.finite_coe_iff.mp (hfin y))

end TauCeti
