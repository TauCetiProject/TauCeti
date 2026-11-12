/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Adjoining an edge to a Serre graph

For two vertices `x` and `y` of a Serre graph `Γ`, the graph `Γ.addEdge x y` has the vertices of
`Γ` and one more geometric edge, joining `x` to `y`. Its darts are `Γ.E ⊕ Bool`: the darts
`Sum.inl e` are those of `Γ`, the new dart `Sum.inr true` runs from `x` to `y`, and its reverse
`Sum.inr false` runs from `y` to `x`. The two vertices may coincide, in which case the new edge is
a loop.

This is the change of one-skeleton made by cutting a face of a polygonal complex along a new
side.

## Main definitions

* `TauCeti.SerreGraph.addEdge`: the graph obtained by adjoining an edge between two vertices.
* `TauCeti.SerreGraph.addEdgeInclusion`: the inclusion of the original graph.
* `TauCeti.SerreGraph.addEdgeGeomEdgeEquiv`: the geometric edges of the new graph are those of the
  original graph and one more.

## Main results

* `TauCeti.SerreGraph.Connected.addEdge`: adjoining an edge to a connected graph gives a connected
  graph.
* `TauCeti.SerreGraph.card_addEdge_geomEdge`: the new graph has one more geometric edge.
-/

public section

universe u v

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph.{u, v}) (x y : Γ.V)

/-- The Serre graph obtained from `Γ` by adjoining one geometric edge between the vertices `x` and
`y`. The dart `Sum.inl e` is the dart `e` of `Γ`, the dart `Sum.inr true` runs from `x` to `y` and
`Sum.inr false` runs from `y` to `x`. It is reducible, so that its vertices and darts are seen to
be `Γ.V` and `Γ.E ⊕ Bool`. -/
abbrev addEdge : SerreGraph.{u, v} where
  V := Γ.V
  E := Γ.E ⊕ Bool
  src := Sum.elim Γ.src fun b => cond b x y
  rev := Sum.map Γ.rev not
  rev_rev e := by rcases e with e | b <;> simp
  rev_ne e := by rcases e with e | b <;> simp [Γ.rev_ne]

variable {Γ x y}

/- The three `src` equations are not simp lemmas: `addEdge` is reducible, so `simp` already
evaluates `src` on the darts `Sum.inl e`, `Sum.inr true` and `Sum.inr false`. -/

theorem addEdge_src_inl (e : Γ.E) : (Γ.addEdge x y).src (.inl e) = Γ.src e := (rfl)

theorem addEdge_src_inr_true : (Γ.addEdge x y).src (.inr true) = x := (rfl)

theorem addEdge_src_inr_false : (Γ.addEdge x y).src (.inr false) = y := (rfl)

@[simp] theorem addEdge_rev_inl (e : Γ.E) :
    (Γ.addEdge x y).rev (.inl e) = .inl (Γ.rev e) := (rfl)

@[simp] theorem addEdge_rev_inr (b : Bool) : (Γ.addEdge x y).rev (.inr b) = .inr !b := (rfl)

@[simp] theorem addEdge_tgt_inl (e : Γ.E) : (Γ.addEdge x y).tgt (.inl e) = Γ.tgt e := (rfl)

@[simp] theorem addEdge_tgt_inr_true : (Γ.addEdge x y).tgt (.inr true) = y := (rfl)

@[simp] theorem addEdge_tgt_inr_false : (Γ.addEdge x y).tgt (.inr false) = x := (rfl)

variable (Γ x y)

/-- The inclusion of a Serre graph into the graph obtained by adjoining an edge. -/
def addEdgeInclusion : Γ.Hom (Γ.addEdge x y) where
  mapV := id
  mapE := Sum.inl
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem addEdgeInclusion_mapV (a : Γ.V) : (Γ.addEdgeInclusion x y).mapV a = a := (rfl)

@[simp] theorem addEdgeInclusion_mapE (e : Γ.E) :
    (Γ.addEdgeInclusion x y).mapE e = .inl e := (rfl)

variable {Γ} in
/-- Adjoining an edge to a connected graph gives a connected graph. -/
theorem Connected.addEdge (h : Γ.Connected) : (Γ.addEdge x y).Connected :=
  (Γ.addEdgeInclusion x y).connected_of_surjective Function.surjective_id h

/-! ### Geometric edges -/

variable {Γ x y} in
/-- Two darts of the original graph lie on the same geometric edge of the new graph exactly when
they do so in the original graph. -/
@[simp] theorem toGeomEdge_addEdge_inl_eq_iff {e e' : Γ.E} :
    (Γ.addEdge x y).toGeomEdge (.inl e) = (Γ.addEdge x y).toGeomEdge (.inl e') ↔
      Γ.toGeomEdge e = Γ.toGeomEdge e' := by
  simp [toGeomEdge_eq_toGeomEdge_iff]

variable {Γ x y} in
/-- A dart of the original graph does not lie on the adjoined geometric edge. -/
theorem toGeomEdge_addEdge_inl_ne_inr (e : Γ.E) (b : Bool) :
    (Γ.addEdge x y).toGeomEdge (.inl e) ≠ (Γ.addEdge x y).toGeomEdge (.inr b) := by
  simp [toGeomEdge_eq_toGeomEdge_iff]

/-- The geometric edges of `Γ.addEdge x y` are those of `Γ` together with the adjoined edge. -/
def addEdgeGeomEdgeEquiv : (Γ.addEdge x y).GeomEdge ≃ Γ.GeomEdge ⊕ Unit where
  toFun := GeomEdge.lift _ (Sum.elim (fun e => .inl (Γ.toGeomEdge e)) fun _ => .inr ()) (by
    rintro (e | _) <;> simp)
  invFun := Sum.elim
    (GeomEdge.lift Γ (fun e => (Γ.addEdge x y).toGeomEdge (.inl e)) fun e => by simp)
    fun _ => (Γ.addEdge x y).toGeomEdge (.inr true)
  left_inv q := by
    obtain ⟨e | b, rfl⟩ := (Γ.addEdge x y).toGeomEdge_surjective q
    · simp
    · cases b
      · simpa using ((Γ.addEdge x y).toGeomEdge_rev (.inr false))
      · simp
  right_inv q := by
    obtain q | ⟨⟩ := q
    · obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective q
      simp
    · simp

@[simp] theorem addEdgeGeomEdgeEquiv_toGeomEdge_inl (e : Γ.E) :
    Γ.addEdgeGeomEdgeEquiv x y ((Γ.addEdge x y).toGeomEdge (.inl e)) = .inl (Γ.toGeomEdge e) :=
  GeomEdge.lift_toGeomEdge ..

@[simp] theorem addEdgeGeomEdgeEquiv_toGeomEdge_inr (b : Bool) :
    Γ.addEdgeGeomEdgeEquiv x y ((Γ.addEdge x y).toGeomEdge (.inr b)) = .inr () :=
  GeomEdge.lift_toGeomEdge ..

/-- Adjoining an edge adds one geometric edge. -/
@[simp] theorem card_addEdge_geomEdge [Finite Γ.GeomEdge] :
    Nat.card (Γ.addEdge x y).GeomEdge = Nat.card Γ.GeomEdge + 1 := by
  rw [Nat.card_congr (Γ.addEdgeGeomEdgeEquiv x y), Nat.card_sum, Nat.card_unique (α := Unit)]

end SerreGraph

end TauCeti
