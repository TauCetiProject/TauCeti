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
graph is the simple support `SerreGraph.supportGraph`, so the number of connected components of
the simple support, which appears in the rank formula for cycle spaces, is the component count of
the multigraph (`SerreGraph.componentCount_endpointGraph`).

When `O` contains at least one dart of every reversal pair, in particular when it is an
orientation, the simple support of `O` is that of all darts, and its components are those of
the multigraph of reversal pairs `SerreGraph.toGraph` (`SerreGraph.componentCount_toGraph`).
Reachability in it is then joinability by a path of darts, and it has exactly one component
precisely when the Serre graph is connected.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1 (graphs and orientations).
* R. Diestel, *Graph Theory*, §1.4 (components) and §1.9 (cycle spaces).
-/

public section

namespace TauCeti.SerreGraph

universe u v

variable (Γ : SerreGraph.{u, v}) (O : Set Γ.E)

/-- The simple graph underlying the multigraph of the darts in `O` is their simple support. -/
def toSimpleGraphEndpointGraphIso :
    (Γ.endpointGraph O).toSimpleGraph ≃g Γ.supportGraph O where
  toEquiv := Equiv.subtypeUnivEquiv fun x => by simp
  map_rel_iff' {x y} := by
    simp [Subtype.ext_iff]

@[simp] theorem toSimpleGraphEndpointGraphIso_apply
    (x : (Γ.endpointGraph O).vertexSet) : Γ.toSimpleGraphEndpointGraphIso O x = x := (rfl)

/-- Two vertices are joined by a walk in the multigraph of the darts in `O` exactly when they
are reachable in the simple support. -/
theorem reachable_endpointGraph_iff (x y : Γ.V) :
    (Γ.endpointGraph O).Reachable x y ↔ (Γ.supportGraph O).Reachable x y := by
  rw [← Graph.toSimpleGraph_reachable_iff (u := ⟨x, by simp⟩) (v := ⟨y, by simp⟩),
    ← (Γ.toSimpleGraphEndpointGraphIso O).reachable_iff]
  simp

/-- The multigraph of the darts in `O` has as many components as its simple support. Loops
and parallel darts do not change the count. -/
theorem componentCount_endpointGraph :
    (Γ.endpointGraph O).componentCount = Nat.card (Γ.supportGraph O).ConnectedComponent := by
  rw [Graph.componentCount_eq_natCard_toSimpleGraph]
  exact Nat.card_congr (Γ.toSimpleGraphEndpointGraphIso O).connectedComponentEquiv

/-- The simple graph underlying the multigraph of reversal pairs is the simple support of all
darts. -/
def toSimpleGraphToGraphIso : Γ.toGraph.toSimpleGraph ≃g Γ.supportGraph Set.univ where
  toEquiv := Equiv.subtypeUnivEquiv fun x => by simp
  map_rel_iff' {x y} := by
    have h : (∃ e, Γ.src e = y ∧ Γ.tgt e = x) ↔ ∃ e, Γ.src e = x ∧ Γ.tgt e = y :=
      ⟨fun ⟨e, h₁, h₂⟩ => ⟨Γ.rev e, by simpa using h₂, by simpa using h₁⟩,
        fun ⟨e, h₁, h₂⟩ => ⟨Γ.rev e, by simpa using h₂, by simpa using h₁⟩⟩
    simp [Subtype.ext_iff, h]

@[simp] theorem toSimpleGraphToGraphIso_apply (x : Γ.toGraph.vertexSet) :
    Γ.toSimpleGraphToGraphIso x = x := (rfl)

variable {Γ O}

/-- A dart set containing at least one dart of every reversal pair has the simple support of
all darts: the simple support does not see the direction of a dart. -/
theorem supportGraph_eq_supportGraph_univ (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    Γ.supportGraph O = Γ.supportGraph Set.univ := by
  ext x y
  simp only [supportGraph_adj, Set.mem_univ, true_and, and_congr_right_iff]
  refine fun _ => ⟨by grind, ?_⟩
  rintro (⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩) <;> grind [Γ.src_rev e, Γ.tgt_rev e, hO e]

/-- For a dart set containing at least one dart of every reversal pair, reachability in the
simple support is joinability by a path of darts. -/
theorem reachable_supportGraph_iff (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) (x y : Γ.V) :
    (Γ.supportGraph O).Reachable x y ↔ Nonempty (Γ.Path x y) := by
  rw [supportGraph_eq_supportGraph_univ hO, ← Γ.reachable_toGraph_iff,
    ← Graph.toSimpleGraph_reachable_iff (u := ⟨x, by simp⟩) (v := ⟨y, by simp⟩),
    ← Γ.toSimpleGraphToGraphIso.reachable_iff]
  simp

/-- For a dart set containing at least one dart of every reversal pair, the components of the
simple support are those of the Serre graph: their number is the component count of its
multigraph of reversal pairs. -/
theorem componentCount_toGraph (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    Γ.toGraph.componentCount = Nat.card (Γ.supportGraph O).ConnectedComponent := by
  rw [Graph.componentCount_eq_natCard_toSimpleGraph, supportGraph_eq_supportGraph_univ hO]
  exact Nat.card_congr Γ.toSimpleGraphToGraphIso.connectedComponentEquiv

/-- For a dart set containing at least one dart of every reversal pair, the multigraph of its
darts and the multigraph of reversal pairs have the same number of components. -/
theorem componentCount_endpointGraph_eq_componentCount_toGraph
    (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    (Γ.endpointGraph O).componentCount = Γ.toGraph.componentCount := by
  rw [Γ.componentCount_endpointGraph, componentCount_toGraph hO]

/-- For a dart set containing at least one dart of every reversal pair, the simple support has
exactly one component precisely when the Serre graph is connected; an empty graph has none. -/
theorem card_connectedComponent_supportGraph_eq_one_iff (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    Nat.card (Γ.supportGraph O).ConnectedComponent = 1 ↔ Γ.Connected := by
  rw [← componentCount_toGraph hO, Graph.componentCount_eq_one_iff, Γ.connected_toGraph_iff]

/-- An orientation has the simple support of all darts. -/
theorem IsOrientation.supportGraph_eq_supportGraph_univ (hO : Γ.IsOrientation O) :
    Γ.supportGraph O = Γ.supportGraph Set.univ :=
  SerreGraph.supportGraph_eq_supportGraph_univ hO.mem_or_rev_mem

/-- For an orientation, reachability in the simple support is joinability by a path of
darts. -/
theorem IsOrientation.reachable_supportGraph_iff (hO : Γ.IsOrientation O) (x y : Γ.V) :
    (Γ.supportGraph O).Reachable x y ↔ Nonempty (Γ.Path x y) :=
  SerreGraph.reachable_supportGraph_iff hO.mem_or_rev_mem x y

/-- The components of the simple support of an orientation are those of the Serre graph: their
number is the component count of its multigraph of reversal pairs. -/
theorem IsOrientation.componentCount_toGraph (hO : Γ.IsOrientation O) :
    Γ.toGraph.componentCount = Nat.card (Γ.supportGraph O).ConnectedComponent :=
  SerreGraph.componentCount_toGraph hO.mem_or_rev_mem

/-- For an orientation, the multigraph of its darts and the multigraph of reversal pairs have
the same number of components. -/
theorem IsOrientation.componentCount_endpointGraph (hO : Γ.IsOrientation O) :
    (Γ.endpointGraph O).componentCount = Γ.toGraph.componentCount :=
  componentCount_endpointGraph_eq_componentCount_toGraph hO.mem_or_rev_mem

/-- The simple support of an orientation has exactly one component precisely when the Serre
graph is connected; an empty graph has none. -/
theorem IsOrientation.card_connectedComponent_supportGraph_eq_one_iff
    (hO : Γ.IsOrientation O) :
    Nat.card (Γ.supportGraph O).ConnectedComponent = 1 ↔ Γ.Connected :=
  SerreGraph.card_connectedComponent_supportGraph_eq_one_iff hO.mem_or_rev_mem

end TauCeti.SerreGraph
