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

An equivalence relation `r` is presented as the graph `SimpleGraph.fromRel r`, and
`Setoid.sameAtomicType_fromRel_iff` describes atomic types there by equalities and
`r`-relations. Two such graphs are isomorphic structures exactly when the equivalence relations
are isomorphic (`Setoid.nonempty_equiv_fromRel_iff`).
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

/-- In the structure of a simple graph, the adjacency symbol holds of a pair exactly when its
entries are adjacent. -/
@[simp]
theorem relMap_adj (G : SimpleGraph V) (x y : V) :
    letI := G.structure
    RelMap Language.adj ![x, y] ↔ G.Adj x y :=
  Iff.rfl

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

namespace Setoid

open SimpleGraph

variable {r : Setoid V} {s : Setoid W}

variable (r s) in
/-- Two tuples have the same atomic type in the graphs of equivalence relations exactly when they
have the same equalities and the same relations between their entries. -/
theorem sameAtomicType_fromRel_iff {n : ℕ} (a : Fin n → V) (b : Fin n → W) :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    TauCeti.SameAtomicType (L := Language.graph) a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i j, r (a i) (a j) ↔ s (b i) (b j) := by
  rw [SimpleGraph.sameAtomicType_iff]
  refine and_congr_right fun heq => forall₂_congr fun i j => ?_
  by_cases h : a i = a j
  · simp [h, (heq i j).mp h]
  · simp [h, mt (heq i j).mpr h, r.comm' (x := a j), s.comm' (x := b j)]

variable (r s) in
/-- The graphs of two equivalence relations are isomorphic structures in the language of graphs
exactly when the relations are isomorphic. -/
theorem nonempty_equiv_fromRel_iff :
    (letI := (fromRel r).structure; letI := (fromRel s).structure
      Nonempty (V ≃[Language.graph] W)) ↔ Nonempty (⇑r ≃r ⇑s) := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  refine ⟨fun ⟨f⟩ => ⟨⟨f.toEquiv, fun {x y} => ?_⟩⟩, fun ⟨e⟩ =>
    ⟨Iso.toLanguageEquiv ⟨e.toEquiv, fun {_ _} => by
      simp only [fromRel_adj, RelIso.coe_fn_toEquiv, ne_eq, e.injective.eq_iff,
        e.map_rel_iff]⟩⟩⟩
  -- The pair `![x, y]` and its image under `f` have the same atomic type.
  have h : TauCeti.SameAtomicType (L := Language.graph) ![x, y] (f ∘ ![x, y]) :=
    (TauCeti.sameAtomicType_iff _ _).mpr
      ⟨fun _ _ => f.injective.eq_iff.symm, fun R g => (f.map_rel R _).symm⟩
  exact (((sameAtomicType_fromRel_iff r s _ _).mp h).2 0 1).symm

end Setoid
