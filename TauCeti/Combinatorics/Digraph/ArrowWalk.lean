/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Digraph.Orientation
public import TauCeti.Combinatorics.Digraph.Basic
public import TauCeti.Combinatorics.Network.Walk
public import TauCeti.Combinatorics.Quiver.Reachable

/-!
# Digraphs as arrow families

The *adjacency arrow family* `Digraph.AdjHom D` of a digraph `D` has a single arrow from `v` to
`w` exactly when `D.Adj v w`; loops are retained, and at most one arrow runs from any vertex to
any other. Directed walks along it (`TauCeti.ArrowWalk`) are the objects on which the network
theory runs, including the directed forms of Menger's theorem, so this family is how statements
about arrow families specialize to digraphs.

This file identifies the notions of the arrow-family theory with their digraph counterparts. The
arrows are the ordered pairs of adjacent vertices, and a walk is determined by its vertex
sequence, which can be any list of vertices in which consecutive vertices are adjacent. Directed
reachability along the family is the reflexive transitive closure of `D.Adj`. Deleting a set `X`
of vertices corresponds to avoiding it: reachability in the digraph induced on the complement of
`X` is reachability along the family through walks visiting no vertex of `X`. Deleting the arrows
of a digraph `E` corresponds to avoiding the arrows joining pairs adjacent in `E`: reachability in
`D \ E` is reachability along the family without those arrows. Finally, the zigzags of arrows,
which define the weakly connected components, are the walks of the simple graph
`D.toSimpleGraphInclusive` obtained by forgetting orientations.

## Main definitions

* `Digraph.AdjHom D`: the adjacency arrow family of `D`.
* `Digraph.sigmaAdjHomEquiv`: the arrows of the family are the ordered pairs of adjacent vertices.
* `Digraph.arrowWalkEquiv`: the walks from `s` to `t` are the lists of vertices from `s` to `t` in
  which consecutive vertices are adjacent.

## Main results

* `Digraph.nonempty_arrowWalk_iff_reflTransGen`: reachability along the adjacency arrow family is
  the reflexive transitive closure of `D.Adj`.
* `Digraph.isStronglyConnected_iff`: the family is strongly connected exactly when every vertex
  reaches every other vertex along `D.Adj`.
* `Digraph.reflTransGen_induce_compl_iff`: reachability after deleting a set `X` of vertices is
  reachability along the family avoiding `X`.
* `Digraph.reflTransGen_sdiff_iff`: reachability after deleting the arrows of a digraph `E` is
  reachability along the family without the arrows joining pairs adjacent in `E`.
* `Digraph.weaklyConnectedComponent_mk_eq_mk_iff`: two vertices lie in the same weakly connected
  component of the family exactly when they are reachable in `D.toSimpleGraphInclusive`.
-/

public section

open TauCeti Relation

universe u

namespace Digraph

variable {V : Type u} (D : Digraph V)

/-- The adjacency arrow family of a digraph: a single arrow from `v` to `w` exactly when
`D.Adj v w`. -/
abbrev AdjHom (v w : V) : Type :=
  PLift (D.Adj v w)

variable {D} {s t v w : V}

/-- Some arrow of the adjacency arrow family runs from `v` to `w` exactly when `D.Adj v w`. -/
theorem nonempty_adjHom_iff : Nonempty (D.AdjHom v w) ↔ D.Adj v w := by
  simp

/-- No arrow of the adjacency arrow family runs from `v` to `w` exactly when `¬D.Adj v w`. -/
theorem isEmpty_adjHom_iff : IsEmpty (D.AdjHom v w) ↔ ¬D.Adj v w := by
  simp

/-! ### Arrows and walks -/

variable (D) in
/-- The arrows of the adjacency arrow family, recorded with their endpoints, are the ordered pairs
of adjacent vertices. -/
def sigmaAdjHomEquiv : (Σ v w, D.AdjHom v w) ≃ {p : V × V // D.Adj p.1 p.2} where
  toFun a := ⟨(a.1, a.2.1), a.2.2.down⟩
  invFun p := ⟨p.1.1, p.1.2, ⟨p.2⟩⟩
  left_inv _ := (rfl)
  right_inv _ := (rfl)

@[simp]
theorem sigmaAdjHomEquiv_apply_coe (a : Σ v w, D.AdjHom v w) :
    (sigmaAdjHomEquiv D a : V × V) = (a.1, a.2.1) :=
  (rfl)

@[simp]
theorem sigmaAdjHomEquiv_symm_apply (p : {p : V × V // D.Adj p.1 p.2}) :
    (sigmaAdjHomEquiv D).symm p = ⟨p.1.1, p.1.2, ⟨p.2⟩⟩ :=
  (rfl)

/-- Consecutive vertices of a walk along the adjacency arrow family are adjacent. -/
theorem isChain_vertices (p : ArrowWalk D.AdjHom s t) : p.vertices.IsChain D.Adj := by
  simpa using p.isChain_vertices

variable (D) in
/-- The walks along the adjacency arrow family from `s` to `t` are the lists of vertices starting
at `s` and ending at `t` in which consecutive vertices are adjacent, through their vertex
sequences. -/
noncomputable def arrowWalkEquiv (s t : V) :
    ArrowWalk D.AdjHom s t ≃
      {l : List V // l.IsChain D.Adj ∧ l.head? = some s ∧ l.getLast? = some t} :=
  Equiv.ofBijective (fun p ↦ ⟨p.vertices, isChain_vertices p,
      @Quiver.Path.vertices_head? V ⟨D.AdjHom⟩ s t p, p.vertices_getLast?⟩)
    ⟨fun _ _ h ↦ ArrowWalk.vertices_injective (congrArg Subtype.val h), fun l ↦
      (ArrowWalk.exists_vertices_eq_of_isChain (by simpa using l.2.1) l.2.2.1 l.2.2.2).imp
        fun _ hp ↦ Subtype.ext hp⟩

@[simp]
theorem arrowWalkEquiv_apply_coe (p : ArrowWalk D.AdjHom s t) :
    (arrowWalkEquiv D s t p : List V) = p.vertices :=
  (rfl)

@[simp]
theorem vertices_arrowWalkEquiv_symm_apply
    (l : {l : List V // l.IsChain D.Adj ∧ l.head? = some s ∧ l.getLast? = some t}) :
    ((arrowWalkEquiv D s t).symm l).vertices = l := by
  rw [← arrowWalkEquiv_apply_coe, Equiv.apply_symm_apply]

/-! ### Reachability -/

/-- Reachability along the adjacency arrow family is the reflexive transitive closure of
adjacency. -/
theorem nonempty_arrowWalk_iff_reflTransGen :
    Nonempty (ArrowWalk D.AdjHom s t) ↔ ReflTransGen D.Adj s t :=
  (@Quiver.reachable_iff_reflTransGen V ⟨D.AdjHom⟩ s t).trans <| by
    simp only [nonempty_plift, nonempty_prop]

/-- The adjacency arrow family is strongly connected exactly when every vertex reaches every other
vertex along adjacency. -/
theorem isStronglyConnected_iff :
    @Quiver.IsStronglyConnected V ⟨D.AdjHom⟩ ↔ ∀ v w, ReflTransGen D.Adj v w :=
  forall₂_congr fun _ _ ↦ nonempty_arrowWalk_iff_reflTransGen

/-! ### Deleting vertices -/

/-- Two vertices of a set `S` are related by the reflexive transitive closure of adjacency in the
digraph induced on `S` exactly when some walk along the adjacency arrow family of `D` joins them
through vertices of `S`. -/
theorem reflTransGen_induce_iff {S : Set V} {s t : S} :
    ReflTransGen (D.induce S).Adj s t ↔
      ∃ p : ArrowWalk D.AdjHom s t, ∀ v ∈ p.vertices, v ∈ S := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨.nil _, by simp⟩
    | tail _ hxy ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.cons ⟨hxy⟩, fun v hv ↦ ?_⟩
      rw [ArrowWalk.vertices_cons, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at hv
      exact hv.elim (hp v) fun hv ↦ hv ▸ Subtype.prop _
  · rintro ⟨p, hp⟩
    -- Generalize the target, a vertex of `S`, to an arbitrary vertex lying in `S`.
    suffices h : ∀ {x : V} (hx : x ∈ S) (p : ArrowWalk D.AdjHom s x),
        (∀ v ∈ p.vertices, v ∈ S) → ReflTransGen (D.induce S).Adj s ⟨x, hx⟩ from h t.2 p hp
    intro x hx p hp
    induction p with
    | nil => rfl
    | cons p e ih =>
      have hp' (v : V) (hv : v ∈ ArrowWalk.vertices p) : v ∈ S := hp v <| by
        rw [ArrowWalk.vertices_cons, List.concat_eq_append, List.mem_append]
        exact .inl hv
      exact (ih (hp' _ (@Quiver.Path.end_mem_vertices V ⟨D.AdjHom⟩ _ _ p)) hp').tail e.down

/-- Reachability after deleting a set `X` of vertices, in the digraph induced on its complement,
is reachability along the adjacency arrow family through walks avoiding `X`. -/
theorem reflTransGen_induce_compl_iff {X : Set V} {s t : ↥Xᶜ} :
    ReflTransGen (D.induce Xᶜ).Adj s t ↔ ReachableAvoiding D.AdjHom X s t := by
  simp only [reflTransGen_induce_iff, reachableAvoiding_def, Set.mem_compl_iff]

/-! ### Deleting arrows -/

/-- Reachability after deleting the arrows of a digraph `E` is reachability along the adjacency
arrow family of `D` without the arrows joining pairs adjacent in `E`. -/
theorem reflTransGen_sdiff_iff {E : Digraph V} :
    ReflTransGen (D \ E).Adj s t ↔
      ReachableWithout (Q := D.AdjHom) {a | E.Adj a.1 a.2.1} s t := by
  have h : (D \ E).Adj = fun x y ↦
      Nonempty (WithoutHom (Q := D.AdjHom) {a | E.Adj a.1 a.2.1} x y) := by
    ext x y
    simp [sdiff_adj]
  rw [reachableWithout_iff_nonempty_arrowWalk, h]
  exact (@Quiver.reachable_iff_reflTransGen V ⟨WithoutHom _⟩ s t).symm

/-! ### Weak connectivity -/

/-- The simple graph underlying the adjacency arrow family is the simple graph obtained from `D`
by forgetting orientations. -/
@[simp]
theorem underlyingGraph_adjHom :
    @TauCeti.Quiver.underlyingGraph V ⟨D.AdjHom⟩ = D.toSimpleGraphInclusive := by
  ext v w
  simp [toSimpleGraphInclusive, TauCeti.Quiver.underlyingGraph_adj]

/-- Two vertices lie in the same weakly connected component of the adjacency arrow family exactly
when they are reachable in the simple graph obtained from `D` by forgetting orientations. -/
theorem weaklyConnectedComponent_mk_eq_mk_iff :
    @Quiver.WeaklyConnectedComponent.mk V ⟨D.AdjHom⟩ v =
        @Quiver.WeaklyConnectedComponent.mk V ⟨D.AdjHom⟩ w ↔
      D.toSimpleGraphInclusive.Reachable v w := by
  rw [@TauCeti.Quiver.weaklyConnectedComponent_mk_eq_mk_iff V ⟨D.AdjHom⟩, underlyingGraph_adjHom]

end Digraph
