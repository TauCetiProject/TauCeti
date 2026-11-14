/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Forest
public import TauCeti.Combinatorics.Graph.Serre.Multigraph

/-!
# Component counts of dart sets of a Serre graph

A set `O` of darts of a Serre graph is a multigraph on all the vertices,
`SerreGraph.endpointGraph`, whose edges are the darts of `O` themselves. Its underlying simple
graph is the simple support `SerreGraph.supportGraph`, so the two have the same reachability and
connectedness, and the number of connected components of the simple support, which appears in
the rank formula for cycle spaces, is the component count of the multigraph
(`SerreGraph.componentCount_endpointGraph_eq_card_connectedComponent_supportGraph`).

When `O` contains at least one dart of every reversal pair, in particular when it is an
orientation, the number of connected components of the simple support is the component count of
the multigraph of reversal pairs `SerreGraph.toGraph`
(`SerreGraph.componentCount_toGraph_eq_card_connectedComponent_supportGraph`).

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1 (graphs and orientations).
* R. Diestel, *Graph Theory*, §1.4 (components) and §1.9 (cycle spaces).
-/

public section

namespace TauCeti.SerreGraph

universe u v

variable (Γ : SerreGraph.{u, v}) (O : Set Γ.E)

/-- The simple graph underlying the multigraph of the darts in `O` is their simple support. -/
def toSimpleGraphEndpointGraphIsoSupportGraph :
    (Γ.endpointGraph O).toSimpleGraph ≃g Γ.supportGraph O where
  toEquiv := Equiv.subtypeUnivEquiv fun x => by simp
  map_rel_iff' {x y} := by
    simp [Subtype.ext_iff]

@[simp] theorem toSimpleGraphEndpointGraphIsoSupportGraph_apply
    (x : (Γ.endpointGraph O).vertexSet) :
    Γ.toSimpleGraphEndpointGraphIsoSupportGraph O x = x := (rfl)

@[simp] theorem coe_toSimpleGraphEndpointGraphIsoSupportGraph_symm_apply (x : Γ.V) :
    ((Γ.toSimpleGraphEndpointGraphIsoSupportGraph O).symm x : Γ.V) = x := (rfl)

/-- Two vertices are joined by a walk in the multigraph of the darts in `O` exactly when they
are reachable in the simple support. -/
theorem reachable_endpointGraph_iff_reachable_supportGraph (x y : Γ.V) :
    (Γ.endpointGraph O).Reachable x y ↔ (Γ.supportGraph O).Reachable x y := by
  rw [← Graph.toSimpleGraph_reachable_iff (u := ⟨x, by simp⟩) (v := ⟨y, by simp⟩),
    ← (Γ.toSimpleGraphEndpointGraphIsoSupportGraph O).reachable_iff]
  simp

/-- The multigraph of the darts in `O` is connected exactly when its simple support is. -/
theorem connected_endpointGraph_iff_connected_supportGraph :
    (Γ.endpointGraph O).Connected ↔ (Γ.supportGraph O).Connected :=
  Graph.connected_iff_toSimpleGraph_connected.trans
    (Γ.toSimpleGraphEndpointGraphIsoSupportGraph O).connected_iff

/-- The multigraph of the darts in `O` has as many components as its simple support. Loops
and parallel darts do not change the count. -/
theorem componentCount_endpointGraph_eq_card_connectedComponent_supportGraph :
    (Γ.endpointGraph O).componentCount = Nat.card (Γ.supportGraph O).ConnectedComponent := by
  rw [Graph.componentCount_eq_natCard_toSimpleGraph]
  exact Nat.card_congr (Γ.toSimpleGraphEndpointGraphIsoSupportGraph O).connectedComponentEquiv

variable {Γ O}

/-- For a dart set containing at least one dart of every reversal pair, the component count of
the multigraph of reversal pairs is the number of connected components of the simple support. -/
theorem componentCount_toGraph_eq_card_connectedComponent_supportGraph
    (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    Γ.toGraph.componentCount = Nat.card (Γ.supportGraph O).ConnectedComponent :=
  (componentCount_endpointGraph_eq_componentCount_toGraph hO).symm.trans
    (Γ.componentCount_endpointGraph_eq_card_connectedComponent_supportGraph O)

/-- For an orientation, the component count of the multigraph of reversal pairs is the number of
connected components of the simple support. -/
theorem IsOrientation.componentCount_toGraph_eq_card_connectedComponent_supportGraph
    (hO : Γ.IsOrientation O) :
    Γ.toGraph.componentCount = Nat.card (Γ.supportGraph O).ConnectedComponent :=
  SerreGraph.componentCount_toGraph_eq_card_connectedComponent_supportGraph hO.mem_or_rev_mem

end TauCeti.SerreGraph
