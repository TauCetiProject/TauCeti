/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.Combinatorics.Network.Walk

/-!
# Walks of a simple graph as directed walks of its adjacency arrow family

The *adjacency arrow family* `SimpleGraph.AdjHom G` of a simple graph `G` has a single arrow from
`v` to `w` exactly when `v` and `w` are adjacent, so every edge gives one arrow in each direction.
Directed walks along it (`TauCeti.ArrowWalk`) are the objects on which the network theory runs,
including the directed forms of Menger's theorem.

This file identifies the walks of `G` with the directed walks of its adjacency arrow family
(`SimpleGraph.Walk.arrowWalkEquiv`). The identification preserves the length and the vertex
sequence, hence paths. Deleting a set `X` of vertices corresponds to avoiding it: reachability in
the subgraph induced on the complement of `X` is reachability along the adjacency arrow family
through walks visiting no vertex of `X`. This is what transports the vertex forms of Menger's
theorem from arrow families to simple graphs.

## Main definitions

* `SimpleGraph.AdjHom G`: the adjacency arrow family of `G`.
* `SimpleGraph.Walk.toArrowWalk`: a walk of `G` as a directed walk.
* `TauCeti.ArrowWalk.toWalk`: a directed walk of the adjacency arrow family as a walk of `G`.
* `SimpleGraph.Walk.arrowWalkEquiv`: these maps are inverse equivalences.

## Main results

* `SimpleGraph.Walk.vertices_toArrowWalk` and `TauCeti.ArrowWalk.support_toWalk`: the
  identification preserves vertex sequences.
* `SimpleGraph.Walk.isPath_toArrowWalk_iff` and `TauCeti.ArrowWalk.isPath_toWalk_iff`: it preserves
  and reflects paths.
* `SimpleGraph.reachable_iff_nonempty_arrowWalk`: reachability in `G` is reachability along the
  adjacency arrow family.
* `SimpleGraph.reachable_induce_iff`: two vertices of a vertex set `S` are reachable in the
  subgraph induced on `S` exactly when some walk between them stays in `S`.
* `SimpleGraph.reachable_induce_compl_iff`: reachability after deleting a set `X` of vertices is
  reachability along the adjacency arrow family avoiding `X`.
-/

public section

open TauCeti

universe u

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- The adjacency arrow family of a simple graph: a single arrow from `v` to `w` exactly when `v`
and `w` are adjacent, so every edge gives one arrow in each direction. -/
abbrev AdjHom (v w : V) : Type :=
  PLift (G.Adj v w)

variable {G}

namespace Walk

/-- A walk of `G` as a directed walk of the adjacency arrow family, visiting the same vertices in
the same order. -/
def toArrowWalk : {u v : V} → G.Walk u v → ArrowWalk G.AdjHom u v
  | _, _, .nil => ArrowWalk.nil _
  | _, _, .cons h p => ((ArrowWalk.nil _).cons ⟨h⟩).comp p.toArrowWalk

variable {u v w : V}

@[simp]
theorem toArrowWalk_nil : (nil : G.Walk u u).toArrowWalk = ArrowWalk.nil u :=
  (rfl)

@[simp]
theorem toArrowWalk_cons (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).toArrowWalk = ((ArrowWalk.nil u).cons ⟨h⟩).comp p.toArrowWalk :=
  (rfl)

/-- The directed walk of a concatenation is the composite of the directed walks. -/
@[simp]
theorem toArrowWalk_append (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).toArrowWalk = p.toArrowWalk.comp q.toArrowWalk := by
  induction p with
  | nil => exact (@Quiver.Path.nil_comp _ ⟨_⟩ _ _ _).symm
  | cons h p ih =>
    rw [cons_append, toArrowWalk_cons, toArrowWalk_cons, ih]
    exact (@Quiver.Path.comp_assoc _ ⟨_⟩ _ _ _ _ _ _ _).symm

/-- The directed walk of a walk visits the vertices of its support, in order. -/
@[simp]
theorem vertices_toArrowWalk (p : G.Walk u v) : p.toArrowWalk.vertices = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [toArrowWalk_cons, ArrowWalk.vertices, @Quiver.Path.vertices_comp _ ⟨_⟩]
    simp only [ArrowWalk.vertices] at ih
    simp [ih]

@[simp]
theorem length_toArrowWalk (p : G.Walk u v) : p.toArrowWalk.length = p.length := by
  have h := congrArg List.length p.vertices_toArrowWalk
  simp only [ArrowWalk.vertices, Quiver.Path.vertices_length, length_support] at h
  simp only [ArrowWalk.length]
  omega

@[simp]
theorem isPath_toArrowWalk_iff {p : G.Walk u v} : p.toArrowWalk.IsPath ↔ p.IsPath := by
  rw [ArrowWalk.isPath_def, vertices_toArrowWalk, isPath_def]

end Walk

end SimpleGraph

namespace TauCeti.ArrowWalk

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- A directed walk of the adjacency arrow family of `G`, as a walk of `G` visiting the same
vertices in the same order. -/
def toWalk {u : V} : {v : V} → ArrowWalk G.AdjHom u v → G.Walk u v
  | _, @Quiver.Path.nil _ .(_) _ => .nil
  | _, @Quiver.Path.cons _ .(_) _ _ _ q e => (toWalk q).concat e.down

variable {u v w : V}

@[simp]
theorem toWalk_nil (u : V) : (nil u : ArrowWalk G.AdjHom u u).toWalk = .nil :=
  (rfl)

@[simp]
theorem toWalk_cons (q : ArrowWalk G.AdjHom u v) (e : G.AdjHom v w) :
    (q.cons e).toWalk = q.toWalk.concat e.down :=
  (rfl)

/-- The walk of a composite directed walk is the concatenation of the walks. -/
@[simp]
theorem toWalk_comp (q : ArrowWalk G.AdjHom u v) (r : ArrowWalk G.AdjHom v w) :
    (q.comp r).toWalk = q.toWalk.append r.toWalk := by
  induction r with
  | nil => exact (Walk.append_nil _).symm
  | cons r e ih =>
    rw [comp, @Quiver.Path.comp_cons _ ⟨_⟩, ← comp, toWalk_cons, toWalk_cons, ih,
      Walk.append_concat]

/-- The walk of a directed walk has the vertices of the directed walk as its support. -/
@[simp]
theorem support_toWalk (q : ArrowWalk G.AdjHom u v) : q.toWalk.support = q.vertices := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    rw [toWalk_cons, Walk.support_concat, ih]
    simp [vertices]

@[simp]
theorem length_toWalk (q : ArrowWalk G.AdjHom u v) : q.toWalk.length = q.length := by
  have h := congrArg List.length q.support_toWalk
  simp only [vertices, Quiver.Path.vertices_length, Walk.length_support] at h
  simp only [length]
  omega

@[simp]
theorem isPath_toWalk_iff {q : ArrowWalk G.AdjHom u v} : q.toWalk.IsPath ↔ q.IsPath := by
  rw [Walk.isPath_def, support_toWalk, isPath_def]

end TauCeti.ArrowWalk

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

namespace Walk

variable {u v : V}

/-- Returning a walk from the adjacency arrow family recovers it. -/
@[simp]
theorem toWalk_toArrowWalk (p : G.Walk u v) : p.toArrowWalk.toWalk = p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [toArrowWalk_cons, ArrowWalk.toWalk_comp, ih, ArrowWalk.toWalk_cons, ArrowWalk.toWalk_nil,
      concat_nil, cons_nil_append]

/-- Every directed walk of the adjacency arrow family is the directed walk of its walk in `G`. -/
@[simp]
theorem toArrowWalk_toWalk (q : ArrowWalk G.AdjHom u v) : q.toWalk.toArrowWalk = q := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    rw [ArrowWalk.toWalk_cons, concat_eq_append, toArrowWalk_append, ih, toArrowWalk_cons,
      toArrowWalk_nil]
    simp only [ArrowWalk.comp]
    rw [@Quiver.Path.comp_nil _ ⟨_⟩, @Quiver.Path.comp_cons _ ⟨_⟩, @Quiver.Path.comp_nil _ ⟨_⟩]
    -- The arrow rebuilt from the adjacency proof of `e` is `e`, by eta for `PLift`.
    rfl

variable (G) in
/-- The walks of `G` between two vertices are the directed walks of the adjacency arrow family
between them, with the same vertex sequences. -/
def arrowWalkEquiv (u v : V) : G.Walk u v ≃ ArrowWalk G.AdjHom u v where
  toFun p := p.toArrowWalk
  invFun q := q.toWalk
  left_inv := toWalk_toArrowWalk
  right_inv := toArrowWalk_toWalk

@[simp]
theorem arrowWalkEquiv_apply (p : G.Walk u v) : arrowWalkEquiv G u v p = p.toArrowWalk :=
  (rfl)

@[simp]
theorem arrowWalkEquiv_symm_apply (q : ArrowWalk G.AdjHom u v) :
    (arrowWalkEquiv G u v).symm q = q.toWalk :=
  (rfl)

theorem toArrowWalk_injective : Function.Injective (toArrowWalk : G.Walk u v → _) :=
  (arrowWalkEquiv G u v).injective

end Walk

theorem _root_.TauCeti.ArrowWalk.toWalk_injective {u v : V} :
    Function.Injective (ArrowWalk.toWalk : ArrowWalk G.AdjHom u v → G.Walk u v) :=
  (Walk.arrowWalkEquiv G u v).symm.injective

/-! ### Reachability -/

variable {s t : V}

/-- Reachability in `G` is reachability along its adjacency arrow family. -/
theorem reachable_iff_nonempty_arrowWalk : G.Reachable s t ↔ Nonempty (ArrowWalk G.AdjHom s t) :=
  (Walk.arrowWalkEquiv G s t).nonempty_congr

/-- Two vertices of a set `S` are reachable in the subgraph induced on `S` exactly when some walk
of `G` between them visits only vertices of `S`. -/
theorem reachable_induce_iff {S : Set V} {s t : S} :
    (G.induce S).Reachable s t ↔ ∃ p : G.Walk s t, ∀ v ∈ p.support, v ∈ S := by
  refine ⟨fun ⟨q⟩ ↦ ⟨q.map (Embedding.induce S).toHom, fun v hv ↦ ?_⟩,
    fun ⟨p, hp⟩ ↦ ⟨p.induce S hp⟩⟩
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 (q.support_map (Embedding.induce S).toHom ▸ hv)
  exact x.2

/-- Reachability along the adjacency arrow family avoiding a set `X` of vertices is the existence
of a walk of `G` visiting no vertex of `X`. -/
theorem reachableAvoiding_adjHom_iff {X : Set V} :
    ReachableAvoiding G.AdjHom X s t ↔ ∃ p : G.Walk s t, ∀ v ∈ p.support, v ∉ X :=
  ⟨fun h ↦ let ⟨q, hq⟩ := reachableAvoiding_def.1 h; ⟨q.toWalk, by simpa using hq⟩,
    fun ⟨p, hp⟩ ↦ reachableAvoiding_def.2 ⟨p.toArrowWalk, by simpa using hp⟩⟩

/-- Reachability after deleting a set `X` of vertices, in the subgraph induced on its complement,
is reachability along the adjacency arrow family avoiding `X`. -/
theorem reachable_induce_compl_iff {X : Set V} {s t : ↥Xᶜ} :
    (G.induce Xᶜ).Reachable s t ↔ ReachableAvoiding G.AdjHom X s t := by
  simp only [reachable_induce_iff, reachableAvoiding_adjHom_iff, Set.mem_compl_iff]

end SimpleGraph
