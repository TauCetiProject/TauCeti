/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Option
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Adjoining and deleting an edge of a Serre graph

For two vertices `x` and `y` of a Serre graph `Γ`, the graph `Γ.addEdge x y` has the vertices of
`Γ` and one more geometric edge, joining `x` to `y`. Its darts are `Γ.E ⊕ Bool`: the darts
`Sum.inl e` are those of `Γ`, the new dart `Sum.inr true` runs from `x` to `y`, and its reverse
`Sum.inr false` runs from `y` to `x`. The two vertices may coincide, in which case the new edge is
a loop.

Conversely, for a dart `d` of `Γ` the graph `Γ.deleteEdge d` has the vertices of `Γ` and the darts
of `Γ` other than `d` and its reverse. The two operations are inverse to each other: deleting the
adjoined edge of `Γ.addEdge x y` gives back `Γ` (`SerreGraph.deleteEdgeAddEdgeEquiv`), and adjoining
an edge from the source to the target of `d` to `Γ.deleteEdge d` gives back `Γ`
(`SerreGraph.deleteEdgeSumEquiv`), compatibly with sources and reversals.

These are the changes of one-skeleton made by cutting a face of a polygonal complex along a new
side, and by merging two faces along a common side.

## Main definitions

* `TauCeti.SerreGraph.addEdge`: the graph obtained by adjoining an edge between two vertices.
* `TauCeti.SerreGraph.addEdgeInclusion`: the inclusion of the original graph.
* `TauCeti.SerreGraph.addEdgeGeomEdgeEquiv`: the geometric edges of the new graph are those of the
  original graph and one more.
* `TauCeti.SerreGraph.deleteEdge`: the graph obtained by deleting the edge of a dart.
* `TauCeti.SerreGraph.deleteEdgeGeomEdgeEquiv`: its geometric edges are the other geometric edges.
* `TauCeti.SerreGraph.deleteEdgeSumEquiv`, `TauCeti.SerreGraph.deleteEdgeAddEdgeEquiv`: deleting an
  edge and adjoining it back, or adjoining an edge and deleting it, gives back the darts.

## Main results

* `TauCeti.SerreGraph.Connected.addEdge`: adjoining an edge to a connected graph gives a connected
  graph.
* `TauCeti.SerreGraph.card_addEdge_geomEdge`: the new graph has one more geometric edge.
* `TauCeti.SerreGraph.card_deleteEdge_geomEdge_add_one`: deleting an edge removes one geometric
  edge.
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

/-! ### Deleting an edge -/

/-- The Serre graph obtained from `Γ` by deleting the geometric edge of the dart `d`: it has the
vertices of `Γ` and the darts of `Γ` other than `d` and its reverse. It is reducible, so that its
vertices are seen to be those of `Γ` and its darts to be darts of `Γ`. -/
abbrev deleteEdge (d : Γ.E) : SerreGraph.{u, v} :=
  Γ.restrict {e | Γ.toGeomEdge e ≠ Γ.toGeomEdge d} fun e he => by simpa using he

/-- The geometric edges of `Γ.deleteEdge d` are those of `Γ` other than the edge of `d`. -/
noncomputable def deleteEdgeGeomEdgeEquiv (d : Γ.E) :
    (Γ.deleteEdge d).GeomEdge ≃ {q : Γ.GeomEdge // q ≠ Γ.toGeomEdge d} := by
  refine Equiv.ofBijective (GeomEdge.lift _ (fun e => ⟨Γ.toGeomEdge e.1, e.2⟩) fun e => by simp)
    ⟨fun q q' hq => ?_, fun ⟨q, hq⟩ => ?_⟩
  · obtain ⟨e, rfl⟩ := (Γ.deleteEdge d).toGeomEdge_surjective q
    obtain ⟨e', rfl⟩ := (Γ.deleteEdge d).toGeomEdge_surjective q'
    simp only [GeomEdge.lift_toGeomEdge, Subtype.mk.injEq, toGeomEdge_eq_toGeomEdge_iff] at hq
    rw [toGeomEdge_eq_toGeomEdge_iff]
    exact hq.imp Subtype.ext Subtype.ext
  · obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective q
    exact ⟨(Γ.deleteEdge d).toGeomEdge ⟨e, hq⟩, GeomEdge.lift_toGeomEdge ..⟩

@[simp] theorem coe_deleteEdgeGeomEdgeEquiv_toGeomEdge (d : Γ.E) (e : (Γ.deleteEdge d).E) :
    (Γ.deleteEdgeGeomEdgeEquiv d ((Γ.deleteEdge d).toGeomEdge e) : Γ.GeomEdge) =
      Γ.toGeomEdge e.1 :=
  congrArg Subtype.val (GeomEdge.lift_toGeomEdge ..)

/-- Deleting an edge removes one geometric edge. -/
theorem card_deleteEdge_geomEdge_add_one [Finite Γ.GeomEdge] (d : Γ.E) :
    Nat.card (Γ.deleteEdge d).GeomEdge + 1 = Nat.card Γ.GeomEdge := by
  classical
  rw [Nat.card_congr (Γ.deleteEdgeGeomEdgeEquiv d), ← Finite.card_option,
    Nat.card_congr (Equiv.optionSubtypeNe _)]

/-- The darts of `Γ` are those of `Γ.deleteEdge d` together with `d`, as `Sum.inr true`, and its
reverse, as `Sum.inr false`. These are the darts of `(Γ.deleteEdge d).addEdge x y`, which is `Γ`
again when `x` and `y` are the source and the target of `d`
(`SerreGraph.src_deleteEdgeSumEquiv`, `SerreGraph.deleteEdgeSumEquiv_rev`). -/
noncomputable def deleteEdgeSumEquiv (d : Γ.E) : (Γ.deleteEdge d).E ⊕ Bool ≃ Γ.E := by
  refine Equiv.ofBijective (Sum.elim Subtype.val fun b => cond b d (Γ.rev d))
    ⟨Subtype.val_injective.sumElim (fun b b' h => ?_) fun e b h => ?_, fun e => ?_⟩
  · cases b <;> cases b' <;>
      first | rfl | exact absurd h (Γ.rev_ne d) | exact absurd h.symm (Γ.rev_ne d)
  · exact e.2 (by cases b <;> simp [h])
  · by_cases he : Γ.toGeomEdge e = Γ.toGeomEdge d
    · rcases Γ.toGeomEdge_eq_toGeomEdge_iff.1 he with rfl | rfl
      exacts [⟨.inr true, rfl⟩, ⟨.inr false, by simp⟩]
    · exact ⟨.inl ⟨e, he⟩, rfl⟩

variable {Γ}

@[simp] theorem deleteEdgeSumEquiv_inl (d : Γ.E) (e : (Γ.deleteEdge d).E) :
    Γ.deleteEdgeSumEquiv d (.inl e) = e.1 :=
  (rfl)

@[simp] theorem deleteEdgeSumEquiv_inr (d : Γ.E) (b : Bool) :
    Γ.deleteEdgeSumEquiv d (.inr b) = cond b d (Γ.rev d) :=
  (rfl)

/-- Adjoining an edge back to `Γ.deleteEdge d` gives back the reversal of `Γ`. -/
theorem deleteEdgeSumEquiv_rev (d : Γ.E) (x y : Γ.V) (e : ((Γ.deleteEdge d).addEdge x y).E) :
    Γ.deleteEdgeSumEquiv d (((Γ.deleteEdge d).addEdge x y).rev e) =
      Γ.rev (Γ.deleteEdgeSumEquiv d e) := by
  rcases e with e | _ | _
  · rfl
  · exact (Γ.rev_rev d).symm
  · rfl

/-- Adjoining an edge from the source to the target of `d` back to `Γ.deleteEdge d` gives back the
sources of `Γ`. -/
theorem src_deleteEdgeSumEquiv {d : Γ.E} {x y : Γ.V} (hx : x = Γ.src d) (hy : y = Γ.tgt d)
    (e : ((Γ.deleteEdge d).addEdge x y).E) :
    Γ.src (Γ.deleteEdgeSumEquiv d e) = ((Γ.deleteEdge d).addEdge x y).src e := by
  rcases e with e | _ | _
  · rfl
  · exact (Γ.src_rev d).trans hy.symm
  · exact hx.symm

variable {x y}

variable (Γ) in
/-- Deleting the adjoined edge of `Γ.addEdge x y`, given by either of its darts, gives back the
darts of `Γ`. -/
def deleteEdgeAddEdgeEquiv {d : (Γ.addEdge x y).E} {b : Bool} (hd : d = .inr b) :
    ((Γ.addEdge x y).deleteEdge d).E ≃ Γ.E where
  toFun e := e.1.getLeft <| by
    obtain ⟨_ | b', he⟩ := e
    · rfl
    · subst hd
      exact absurd (by cases b <;> cases b' <;> simp [toGeomEdge_eq_toGeomEdge_iff]) he
  invFun e := ⟨.inl e, by subst hd; exact toGeomEdge_addEdge_inl_ne_inr e b⟩
  left_inv e := Subtype.ext (Sum.inl_getLeft _ _)
  right_inv _ := rfl

@[simp] theorem inl_deleteEdgeAddEdgeEquiv {d : (Γ.addEdge x y).E} {b : Bool} (hd : d = .inr b)
    (e : ((Γ.addEdge x y).deleteEdge d).E) :
    (.inl (Γ.deleteEdgeAddEdgeEquiv hd e) : Γ.E ⊕ Bool) = e.1 :=
  Sum.inl_getLeft _ _

@[simp] theorem coe_deleteEdgeAddEdgeEquiv_symm {d : (Γ.addEdge x y).E} {b : Bool}
    (hd : d = .inr b) (e : Γ.E) : ((Γ.deleteEdgeAddEdgeEquiv hd).symm e).1 = .inl e :=
  (rfl)

/-- Deleting the adjoined edge gives back the sources of `Γ`. -/
theorem src_deleteEdgeAddEdgeEquiv {d : (Γ.addEdge x y).E} {b : Bool} (hd : d = .inr b)
    (e : ((Γ.addEdge x y).deleteEdge d).E) :
    Γ.src (Γ.deleteEdgeAddEdgeEquiv hd e) = ((Γ.addEdge x y).deleteEdge d).src e := by
  rw [restrict_src, ← inl_deleteEdgeAddEdgeEquiv hd e, addEdge_src_inl]

/-- Deleting the adjoined edge gives back the reversal of `Γ`. -/
theorem deleteEdgeAddEdgeEquiv_rev {d : (Γ.addEdge x y).E} {b : Bool} (hd : d = .inr b)
    (e : ((Γ.addEdge x y).deleteEdge d).E) :
    Γ.deleteEdgeAddEdgeEquiv hd (((Γ.addEdge x y).deleteEdge d).rev e) =
      Γ.rev (Γ.deleteEdgeAddEdgeEquiv hd e) := by
  apply Sum.inl_injective
  rw [inl_deleteEdgeAddEdgeEquiv, restrict_rev_val, ← inl_deleteEdgeAddEdgeEquiv hd e,
    addEdge_rev_inl]

end SerreGraph

end TauCeti
