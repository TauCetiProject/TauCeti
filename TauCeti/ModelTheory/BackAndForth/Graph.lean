/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.AtomicType
public import Mathlib.ModelTheory.Graph
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Simple graphs as relational structures

A simple graph `G` is a structure in the language of graphs through Mathlib's `G.structure`.
A graph isomorphism is then an isomorphism of these structures, and two tuples of vertices have
the same atomic type exactly when they have the same pattern of equalities and the same pattern
of adjacencies. These two facts reduce back-and-forth computations on concrete graphs to
statements about vertices and edges.
-/

public section

universe u u'

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {V : Type u} {W : Type u'}

namespace SimpleGraph

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph isomorphism, as an isomorphism of the corresponding structures in the language of
graphs. -/
def Iso.toLanguageEquiv (e : G ≃g H) :
    letI := G.structure
    letI := H.structure
    V ≃[Language.graph] W :=
  letI := G.structure
  letI := H.structure
  { toEquiv := e.toEquiv
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun
      | .adj, _ => e.map_rel_iff }

/-- The isomorphism of structures induced by a graph isomorphism acts as the graph isomorphism. -/
@[simp]
theorem Iso.toLanguageEquiv_apply (e : G ≃g H) (v : V) :
    letI := G.structure
    letI := H.structure
    e.toLanguageEquiv v = e v := (rfl)

variable (G H) in
/-- Two tuples of vertices have the same atomic type in the language of graphs exactly when they
have the same equalities and the same adjacencies between their entries. -/
theorem sameAtomicType_iff {n : ℕ} (a : Fin n → V) (b : Fin n → W) :
    letI := G.structure
    letI := H.structure
    TauCeti.SameAtomicType (L := Language.graph) a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i j, G.Adj (a i) (a j) ↔ H.Adj (b i) (b j) := by
  let := G.structure
  let := H.structure
  rw [TauCeti.sameAtomicType_iff]
  refine and_congr_right fun _ => ⟨fun h i j => h Language.adj ![i, j], fun h => ?_⟩
  rintro _ ⟨⟩ f
  exact h (f 0) (f 1)

end SimpleGraph
