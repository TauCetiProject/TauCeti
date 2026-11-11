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

A set `O` of darts of a Serre graph is a multigraph on all the vertices: its edges are the
darts of `O` themselves, each joining its source to its target, so loops and parallel darts
are retained. This is `SerreGraph.endpointGraph`. Its underlying simple graph is the simple
support `SerreGraph.supportGraph`, so the number of connected components of the simple
support, which appears in the rank formula for cycle spaces, is the component count of the
multigraph (`SerreGraph.componentCount_endpointGraph`).

When `O` contains at least one dart of every reversal pair, in particular when it is an
orientation, the simple support of `O` is that of all darts, and its components are those of
the multigraph of reversal pairs `SerreGraph.toGraph`
(`SerreGraph.IsOrientation.componentCount_toGraph`). Reachability in it is then joinability by
a path of darts, and it has exactly one component precisely when the Serre graph is connected.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1 (graphs and orientations).
* R. Diestel, *Graph Theory*, §1.4 (components) and §1.9 (cycle spaces).
-/

public section

namespace TauCeti.SerreGraph

universe u v

variable (Γ : SerreGraph.{u, v}) (O : Set Γ.E)

/-- The multigraph on all vertices whose edges are the darts in `O`, each joining its source
and its target. Loops and parallel darts remain distinct edges. -/
def endpointGraph : Graph Γ.V Γ.E where
  vertexSet := Set.univ
  edgeSet := O
  IsLink e x y := e ∈ O ∧ s(Γ.src e, Γ.tgt e) = s(x, y)
  isLink_symm _ _ := ⟨fun _ _ h => ⟨h.1, h.2.trans Sym2.eq_swap⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h k := by
    rcases Sym2.eq_iff.mp (h.2.symm.trans k.2) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  edge_mem_iff_exists_isLink e := ⟨fun he => ⟨_, _, he, rfl⟩, fun ⟨_, _, he, _⟩ => he⟩
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

@[simp] theorem vertexSet_endpointGraph : (Γ.endpointGraph O).vertexSet = Set.univ := (rfl)

@[simp] theorem edgeSet_endpointGraph : (Γ.endpointGraph O).edgeSet = O := (rfl)

@[simp] theorem endpointGraph_isLink (e : Γ.E) (x y : Γ.V) :
    (Γ.endpointGraph O).IsLink e x y ↔ e ∈ O ∧ s(Γ.src e, Γ.tgt e) = s(x, y) := Iff.rfl

/-- A chosen dart is an edge of the multigraph joining its source and its target. -/
theorem endpointGraph_isLink_src_tgt {e : Γ.E} (he : e ∈ O) :
    (Γ.endpointGraph O).IsLink e (Γ.src e) (Γ.tgt e) :=
  ⟨he, rfl⟩

/-- A dart is a loop of the multigraph exactly when it is chosen and its ends coincide. -/
theorem endpointGraph_isLoopAt_iff (e : Γ.E) (x : Γ.V) :
    (Γ.endpointGraph O).IsLoopAt e x ↔ e ∈ O ∧ Γ.src e = x ∧ Γ.tgt e = x := by
  simp [← Graph.isLink_self_iff]

/-- Two vertices are adjacent in the multigraph exactly when a chosen dart joins them, in
either direction. -/
theorem endpointGraph_adj (x y : Γ.V) :
    (Γ.endpointGraph O).Adj x y ↔
      (∃ e ∈ O, Γ.src e = x ∧ Γ.tgt e = y) ∨ ∃ e ∈ O, Γ.src e = y ∧ Γ.tgt e = x := by
  simp only [Graph.Adj, endpointGraph_isLink, Sym2.eq_iff]
  grind

/-- Enlarging the dart set enlarges the multigraph. -/
theorem endpointGraph_mono {O O' : Set Γ.E} (h : O ⊆ O') :
    Γ.endpointGraph O ≤ Γ.endpointGraph O' :=
  ⟨subset_rfl, fun _ _ _ hl => ⟨h hl.1, hl.2⟩⟩

/-- The simple graph underlying the multigraph of the darts in `O` is their simple support. -/
def toSimpleGraphEndpointGraphIso :
    (Γ.endpointGraph O).toSimpleGraph ≃g Γ.supportGraph O where
  toEquiv := Equiv.subtypeUnivEquiv fun x => by simp
  map_rel_iff' {x y} := by
    simp [endpointGraph_adj, Subtype.ext_iff]

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

/-- A dart set containing at least one dart of every reversal pair has the simple support of
all darts: the simple support does not see the direction of a dart. -/
theorem supportGraph_eq_supportGraph_univ {O : Set Γ.E} (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    Γ.supportGraph O = Γ.supportGraph Set.univ := by
  ext x y
  simp only [supportGraph_adj, Set.mem_univ, true_and, and_congr_right_iff]
  refine fun _ => ⟨by grind, ?_⟩
  rintro (⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩) <;> grind [Γ.src_rev e, Γ.tgt_rev e, hO e]

/-- An orientation has the simple support of all darts. -/
theorem IsOrientation.supportGraph_eq_supportGraph_univ {O : Set Γ.E}
    (hO : Γ.IsOrientation O) :
    Γ.supportGraph O = Γ.supportGraph Set.univ :=
  Γ.supportGraph_eq_supportGraph_univ fun e =>
    (em (e ∈ O)).imp_right (IsOrientation.mem_rev_iff Γ hO e).mpr

/-- The simple graph underlying the multigraph of reversal pairs is the simple support of all
darts. -/
def toSimpleGraphToGraphIso : Γ.toGraph.toSimpleGraph ≃g Γ.supportGraph Set.univ where
  toEquiv := Equiv.subtypeUnivEquiv fun x => by simp
  map_rel_iff' {x y} := by
    have h : (∃ e, Γ.src e = y ∧ Γ.tgt e = x) ↔ ∃ e, Γ.src e = x ∧ Γ.tgt e = y :=
      ⟨fun ⟨e, h₁, h₂⟩ => ⟨Γ.rev e, by simpa using h₂, by simpa using h₁⟩,
        fun ⟨e, h₁, h₂⟩ => ⟨Γ.rev e, by simpa using h₂, by simpa using h₁⟩⟩
    simp [toGraph_adj, Subtype.ext_iff, h]

@[simp] theorem toSimpleGraphToGraphIso_apply (x : Γ.toGraph.vertexSet) :
    Γ.toSimpleGraphToGraphIso x = x := (rfl)

/-- Two vertices are reachable in the simple support of all darts exactly when a path of darts
joins them. -/
theorem reachable_supportGraph_univ_iff (x y : Γ.V) :
    (Γ.supportGraph Set.univ).Reachable x y ↔ Nonempty (Γ.Path x y) := by
  rw [← Γ.reachable_toGraph_iff,
    ← Graph.toSimpleGraph_reachable_iff (u := ⟨x, by simp⟩) (v := ⟨y, by simp⟩),
    ← Γ.toSimpleGraphToGraphIso.reachable_iff]
  simp

/-- The multigraph of reversal pairs has as many components as the simple support of all
darts. -/
theorem componentCount_toGraph :
    Γ.toGraph.componentCount = Nat.card (Γ.supportGraph Set.univ).ConnectedComponent := by
  rw [Graph.componentCount_eq_natCard_toSimpleGraph]
  exact Nat.card_congr Γ.toSimpleGraphToGraphIso.connectedComponentEquiv

variable {Γ O}

/-- The components of the simple support of an orientation are those of the Serre graph: their
number is the component count of its multigraph of reversal pairs. -/
theorem IsOrientation.componentCount_toGraph (hO : Γ.IsOrientation O) :
    Γ.toGraph.componentCount = Nat.card (Γ.supportGraph O).ConnectedComponent := by
  rw [Γ.componentCount_toGraph, hO.supportGraph_eq_supportGraph_univ]

/-- For an orientation, the multigraph of its darts and the multigraph of reversal pairs have
the same number of components. -/
theorem IsOrientation.componentCount_endpointGraph (hO : Γ.IsOrientation O) :
    (Γ.endpointGraph O).componentCount = Γ.toGraph.componentCount := by
  rw [Γ.componentCount_endpointGraph, hO.componentCount_toGraph]

/-- For an orientation, reachability in the simple support is joinability by a path of
darts. -/
theorem IsOrientation.reachable_supportGraph_iff (hO : Γ.IsOrientation O) (x y : Γ.V) :
    (Γ.supportGraph O).Reachable x y ↔ Nonempty (Γ.Path x y) := by
  rw [hO.supportGraph_eq_supportGraph_univ, Γ.reachable_supportGraph_univ_iff]

/-- The simple support of an orientation has exactly one component precisely when the Serre
graph is connected; an empty graph has none. -/
theorem IsOrientation.card_connectedComponent_supportGraph_eq_one_iff
    (hO : Γ.IsOrientation O) :
    Nat.card (Γ.supportGraph O).ConnectedComponent = 1 ↔ Γ.Connected := by
  rw [← hO.componentCount_toGraph, Graph.componentCount_eq_one_iff, Γ.connected_toGraph_iff]

end TauCeti.SerreGraph
