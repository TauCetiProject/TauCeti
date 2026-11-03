/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Orientation.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected

/-!
# Walks following a multigraph orientation

`Graph.Walk.FollowsOrientation` says that every traversal uses the chosen direction of its
edge. Such walks between actual vertices correspond exactly to directed walks of
`Graph.Orientation.Hom`, via `Graph.Orientation.walkEquiv`. The correspondence retains the
vertex and edge sequences, commutes with concatenation, and preserves paths and cycles.

Unlike the bidirected construction, an orientation has only one arrow per edge identity.
Consequently directed cycles forget to undirected cycles without a separate trail assumption:
the two opposite traversals of one nonloop edge cannot both follow the orientation. Loops and
parallel edges need no exceptions. These identifications allow directed ear and strong
connectivity arguments to return native multigraph walk witnesses. The conversion interface
parallels `Graph.Walk.bidirectedEquiv`, but restricts to walks following the chosen directions.
-/

public section

open TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

namespace Walk

/-- Every edge of the walk is traversed from its chosen tail to its chosen head. -/
def FollowsOrientation {x y : α} (p : G.Walk x y) (o : G.Orientation) : Prop :=
  match p with
  | .nil => True
  | .cons' x y _ e h q =>
    (o.tail ⟨e, h.edge_mem⟩ : α) = x ∧
      (o.head ⟨e, h.edge_mem⟩ : α) = y ∧ q.FollowsOrientation o

variable {o : G.Orientation} {x y z : α}

@[simp]
theorem followsOrientation_nil (x : α) : (nil : G.Walk x x).FollowsOrientation o :=
  True.intro

@[simp]
theorem followsOrientation_cons {e : β} (h : G.IsLink e x y) (p : G.Walk y z) :
    (cons e h p).FollowsOrientation o ↔
      (o.tail ⟨e, h.edge_mem⟩ : α) = x ∧
        (o.head ⟨e, h.edge_mem⟩ : α) = y ∧ p.FollowsOrientation o := Iff.rfl

/-- A single traversal follows the orientation exactly when its endpoints are the chosen
ordered ends. -/
@[simp]
theorem _root_.Graph.IsLink.followsOrientation_toWalk_iff {e : β} (h : G.IsLink e x y) :
    h.toWalk.FollowsOrientation o ↔
      (o.tail ⟨e, h.edge_mem⟩ : α) = x ∧ (o.head ⟨e, h.edge_mem⟩ : α) = y := by
  simp [IsLink.toWalk_eq_cons]

/-- Concatenation follows the orientation exactly when both constituent walks do. -/
@[simp]
theorem followsOrientation_append (p : G.Walk x y) (q : G.Walk y z) :
    (p.append q).FollowsOrientation o ↔ p.FollowsOrientation o ∧ q.FollowsOrientation o := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih, and_assoc]

/-- Reversing both the walk and the orientation preserves following the chosen directions. -/
@[simp]
theorem followsOrientation_reverse (p : G.Walk x y) :
    p.reverse.FollowsOrientation o.reverse ↔ p.FollowsOrientation o := by
  induction p with
  | nil => simp
  | cons e h p ih =>
    simp [reverse_cons, IsLink.toWalk_eq_cons, ih, and_comm, and_left_comm]

/-- A walk following an orientation, viewed as a directed walk on the actual vertices. -/
def toOriented : {x y : α} → (p : G.Walk x y) → (hp : p.FollowsOrientation o) →
    (hx : x ∈ V(G)) → ArrowWalk o.Hom ⟨x, hx⟩ ⟨y, p.end_mem_vertexSet hx⟩
  | _, _, .nil, _, _ => ArrowWalk.nil _
  | _, _, .cons e h p, hp, _ =>
    ((ArrowWalk.nil _).cons
      (⟨⟨e, h.edge_mem⟩, Subtype.ext hp.1, Subtype.ext hp.2.1⟩ : o.Hom _ _)).comp
        (p.toOriented hp.2.2 h.right_mem)

@[simp]
theorem toOriented_nil (hx : x ∈ V(G)) :
    (nil : G.Walk x x).toOriented (o := o) (followsOrientation_nil x) hx = ArrowWalk.nil _ :=
  (rfl)

@[simp]
theorem toOriented_cons {e : β} (h : G.IsLink e x y) (p : G.Walk y z)
    (hp : (cons e h p).FollowsOrientation o) (hx : x ∈ V(G)) :
    (cons e h p).toOriented hp hx =
      ((ArrowWalk.nil _).cons
        (⟨⟨e, h.edge_mem⟩,
          Subtype.ext (followsOrientation_cons h p |>.1 hp).1,
          Subtype.ext (followsOrientation_cons h p |>.1 hp).2.1⟩ : o.Hom _ _)).comp
          (p.toOriented (followsOrientation_cons h p |>.1 hp).2.2 h.right_mem) := (rfl)

-- The conversion depends on a proof about its walk, so equalities of walks must transport
-- that proof too; ordinary rewriting under the conversion cannot build this dependent motive.
private theorem toOriented_congr {p q : G.Walk x y} (h : p = q)
    (hp : p.FollowsOrientation o) (hq : q.FollowsOrientation o) (hx : x ∈ V(G)) :
    p.toOriented hp hx = q.toOriented hq hx := by
  subst q
  rfl

/-- The directed walk of a single traversal is its chosen oriented arrow. -/
@[simp]
theorem _root_.Graph.IsLink.toOriented_toWalk {e : β} (h : G.IsLink e x y)
    (hp : h.toWalk.FollowsOrientation o) (hx : x ∈ V(G)) :
    h.toWalk.toOriented hp hx = (ArrowWalk.nil _).cons
      (⟨⟨e, h.edge_mem⟩,
        Subtype.ext (h.followsOrientation_toWalk_iff.1 hp).1,
        Subtype.ext (h.followsOrientation_toWalk_iff.1 hp).2⟩ : o.Hom _ _) := by
  refine (toOriented_congr h.toWalk_eq_cons hp
    ((followsOrientation_cons h .nil).2
      ⟨(h.followsOrientation_toWalk_iff.1 hp).1,
        (h.followsOrientation_toWalk_iff.1 hp).2, followsOrientation_nil _⟩) hx).trans ?_
  simp only [toOriented_cons, toOriented_nil, Quiver.Path.comp_nil]

/-- Conversion to directed walks commutes with concatenation. -/
@[simp]
theorem toOriented_append (p : G.Walk x y) (q : G.Walk y z)
    (hp : p.FollowsOrientation o) (hq : q.FollowsOrientation o) (hx : x ∈ V(G)) :
    (p.append q).toOriented (followsOrientation_append p q |>.2 ⟨hp, hq⟩) hx =
      (p.toOriented hp hx).comp (q.toOriented hq (p.end_mem_vertexSet hx)) := by
  induction p with
  | nil =>
    exact (toOriented_congr (nil_append q) _ hq hx).trans
      (@Quiver.Path.nil_comp _ ⟨_⟩ _ _ _).symm
  | cons e h p ih =>
    have hp' := (followsOrientation_cons h p).1 hp
    refine (toOriented_congr (cons_append e h p q) _
      ((followsOrientation_cons h (p.append q)).2
        ⟨hp'.1, hp'.2.1, (followsOrientation_append p q).2 ⟨hp'.2.2, hq⟩⟩) hx).trans ?_
    rw [toOriented_cons, ih]
    exact (@Quiver.Path.comp_assoc _ ⟨_⟩ _ _ _ _ _ _ _).symm

end Walk

namespace Orientation

variable (o : G.Orientation)

/-- Include the chosen oriented arrows into the bidirected arrow family. The abbreviation keeps
its identity vertex map reducible, so transported walks retain their endpoint types. -/
abbrev toBidirected : @Prefunctor V(G) ⟨o.Hom⟩ V(G) ⟨G.BidirectedHom⟩ :=
  @Prefunctor.mk V(G) ⟨o.Hom⟩ V(G) ⟨G.BidirectedHom⟩ id fun a ↦ ⟨a.edge.1, a.isLink⟩

@[simp]
theorem toBidirected_obj (x : V(G)) :
    @Prefunctor.obj V(G) ⟨o.Hom⟩ V(G) ⟨G.BidirectedHom⟩ o.toBidirected x = x := (rfl)

@[simp]
theorem toBidirected_map {x y : V(G)} (a : o.Hom x y) :
    @Prefunctor.map V(G) ⟨o.Hom⟩ V(G) ⟨G.BidirectedHom⟩ o.toBidirected x y a =
      ⟨a.edge.1, a.isLink⟩ := (rfl)

/-- A single oriented arrow follows the orientation as an undirected traversal. -/
-- Prefer the arrow fact to expanding the endpoint equalities for an arbitrary traversal.
@[simp high]
theorem Hom.followsOrientation_toWalk {o : G.Orientation} {x y : V(G)} (a : o.Hom x y) :
    a.isLink.toWalk.FollowsOrientation o := by
  simp [congrArg Subtype.val a.tail_eq, congrArg Subtype.val a.head_eq]

/-- Converting a single oriented arrow's underlying traversal recovers that arrow. -/
-- Retain the original arrow rather than rebuilding it with the general single-edge lemma.
@[simp high]
theorem Hom.toOriented_toWalk {o : G.Orientation} {x y : V(G)} (a : o.Hom x y) :
    a.isLink.toWalk.toOriented a.followsOrientation_toWalk x.2 = (ArrowWalk.nil _).cons a := by
  refine (IsLink.toOriented_toWalk a.isLink a.followsOrientation_toWalk x.2).trans ?_
  exact congrArg (fun a ↦ (ArrowWalk.nil _).cons a) (Hom.ext (Subtype.ext rfl))

/-- Forget the directions of a directed walk, retaining each traversed edge identity. -/
def forgetWalk (o : G.Orientation) {x y : V(G)} (p : ArrowWalk o.Hom x y) : G.Walk x y :=
  ArrowWalk.toGraphWalk
    (@Prefunctor.mapPath V(G) ⟨o.Hom⟩ V(G) ⟨G.BidirectedHom⟩ o.toBidirected x y p)

variable {x y z : V(G)}

@[simp]
theorem forgetWalk_nil (x : V(G)) : o.forgetWalk (ArrowWalk.nil x) = .nil := by
  simp [forgetWalk]

@[simp]
theorem forgetWalk_cons (p : ArrowWalk o.Hom x y) (a : o.Hom y z) :
    o.forgetWalk (p.cons a) = (o.forgetWalk p).append a.isLink.toWalk := by
  simp [forgetWalk]

/-- Forgetting directions commutes with composition. -/
@[simp]
theorem forgetWalk_comp (p : ArrowWalk o.Hom x y) (q : ArrowWalk o.Hom y z) :
    o.forgetWalk (p.comp q) = (o.forgetWalk p).append (o.forgetWalk q) := by
  simp [forgetWalk, Prefunctor.mapPath_comp]

/-- Every directed walk follows the orientation after directions are forgotten. -/
@[simp]
theorem followsOrientation_forgetWalk (p : ArrowWalk o.Hom x y) :
    (o.forgetWalk p).FollowsOrientation o := by
  induction p with
  | nil => simp
  | cons p a ih =>
    rw [forgetWalk_cons]
    exact (Walk.followsOrientation_append _ _).2 ⟨ih, a.followsOrientation_toWalk⟩

/-- Forgetting directions retains the length. -/
@[simp]
theorem length_forgetWalk (p : ArrowWalk o.Hom x y) : (o.forgetWalk p).length = p.length := by
  simp [forgetWalk]

/-- Forgetting directions retains the vertex sequence. -/
@[simp]
theorem support_forgetWalk (p : ArrowWalk o.Hom x y) :
    (o.forgetWalk p).support = p.vertices.unattach := by
  rw [forgetWalk, ArrowWalk.support_toGraphWalk,
    ArrowWalk.vertices_mapPath_of_obj_eq_id o.toBidirected rfl]

/-- Forgetting directions retains the edge sequence. -/
@[simp]
theorem edges_forgetWalk (p : ArrowWalk o.Hom x y) :
    (o.forgetWalk p).edges = p.arrows.map (fun a ↦ a.2.2.edge.1) := by
  simp only [forgetWalk, ArrowWalk.edges_toGraphWalk]
  induction p with
  | nil => simp
  | cons p a ih => simp [ih]

/-- Forgetting directions preserves and reflects paths. -/
@[simp]
theorem isPath_forgetWalk_iff (p : ArrowWalk o.Hom x y) :
    (o.forgetWalk p).IsPath ↔ p.IsPath := by
  rw [forgetWalk, ArrowWalk.isPath_toGraphWalk_iff, ArrowWalk.isPath_def,
    ArrowWalk.vertices_mapPath_of_obj_eq_id o.toBidirected rfl, ArrowWalk.isPath_def]

/-- Forgetting directions preserves and reflects cycles. Each edge has only one directed arrow,
so no additional distinct-edge condition is needed. -/
@[simp]
theorem isCycle_forgetWalk_iff {x : V(G)} (p : ArrowWalk o.Hom x x) :
    (o.forgetWalk p).IsCycle ↔ p.IsCycle := by
  have hcycle :
      (ArrowWalk.IsCycle (Q := G.BidirectedHom)
        (@Prefunctor.mapPath V(G) ⟨o.Hom⟩ V(G) ⟨G.BidirectedHom⟩ o.toBidirected x x p)) ↔
      p.IsCycle := by
    simp only [ArrowWalk.isCycle_def, Prefunctor.length_mapPath,
      ArrowWalk.vertices_mapPath_of_obj_eq_id o.toBidirected rfl]
  rw [forgetWalk, ArrowWalk.isCycle_toGraphWalk_iff, hcycle,
    ← ArrowWalk.edges_toGraphWalk, ← forgetWalk, edges_forgetWalk,
    List.nodup_map_iff o.totalHom_edge_val_injective]
  exact and_iff_left_of_imp ArrowWalk.IsCycle.nodup_arrows

end Orientation

namespace Walk

variable {o : G.Orientation} {x y : α}

/-- Converting a walk following the orientation and then forgetting directions recovers it. -/
@[simp]
theorem forgetWalk_toOriented (p : G.Walk x y) (hp : p.FollowsOrientation o)
    (hx : x ∈ V(G)) : o.forgetWalk (p.toOriented hp hx) = p := by
  induction p with
  | nil => simp
  | cons e h p ih => simp [ih, IsLink.toWalk_eq_cons]

/-- Converting the underlying walk of a directed walk recovers the directed walk. -/
@[simp]
theorem toOriented_forgetWalk {x y : V(G)} (p : ArrowWalk o.Hom x y) :
    (o.forgetWalk p).toOriented (o.followsOrientation_forgetWalk p) x.2 = p := by
  induction p with
  | nil =>
    exact (toOriented_congr (o.forgetWalk_nil _) _ (followsOrientation_nil _) _).trans
      (toOriented_nil _)
  | cons p a ih =>
    refine (toOriented_congr (o.forgetWalk_cons p a) _
      ((followsOrientation_append _ _).2
        ⟨o.followsOrientation_forgetWalk p, a.followsOrientation_toWalk⟩) _).trans ?_
    rw [toOriented_append _ _ (o.followsOrientation_forgetWalk p) a.followsOrientation_toWalk,
      ih, Orientation.Hom.toOriented_toWalk]
    simp only [@Quiver.Path.comp_cons _ ⟨o.Hom⟩, @Quiver.Path.comp_nil _ ⟨o.Hom⟩]

/-- Conversion to a directed walk retains length. -/
@[simp]
theorem length_toOriented (p : G.Walk x y) (hp : p.FollowsOrientation o) (hx : x ∈ V(G)) :
    (p.toOriented hp hx).length = p.length := by
  simpa only [forgetWalk_toOriented] using (o.length_forgetWalk (p.toOriented hp hx)).symm

/-- Conversion to a directed walk retains the vertex sequence. -/
@[simp]
theorem vertices_toOriented (p : G.Walk x y) (hp : p.FollowsOrientation o) (hx : x ∈ V(G)) :
    (p.toOriented hp hx).vertices.unattach = p.support := by
  simpa only [forgetWalk_toOriented] using (o.support_forgetWalk (p.toOriented hp hx)).symm

/-- Conversion to a directed walk retains the edge sequence. -/
@[simp]
theorem edges_toOriented (p : G.Walk x y) (hp : p.FollowsOrientation o) (hx : x ∈ V(G)) :
    (p.toOriented hp hx).arrows.map (fun a ↦ a.2.2.edge.1) = p.edges := by
  simpa only [forgetWalk_toOriented] using (o.edges_forgetWalk (p.toOriented hp hx)).symm

/-- Conversion to a directed walk preserves and reflects paths. -/
@[simp]
theorem isPath_toOriented_iff (p : G.Walk x y) (hp : p.FollowsOrientation o)
    (hx : x ∈ V(G)) : (p.toOriented hp hx).IsPath ↔ p.IsPath := by
  simpa only [forgetWalk_toOriented] using (o.isPath_forgetWalk_iff (p.toOriented hp hx)).symm

/-- Conversion to a directed walk preserves and reflects cycles. -/
@[simp]
theorem isCycle_toOriented_iff (p : G.Walk x x) (hp : p.FollowsOrientation o)
    (hx : x ∈ V(G)) : (p.toOriented hp hx).IsCycle ↔ p.IsCycle := by
  simpa only [forgetWalk_toOriented] using (o.isCycle_forgetWalk_iff (p.toOriented hp hx)).symm

end Walk

namespace Orientation

/-- Directed walks of an orientation are exactly the native walks following its directions. -/
def walkEquiv (o : G.Orientation) (x y : V(G)) :
    {p : G.Walk x y // p.FollowsOrientation o} ≃ ArrowWalk o.Hom x y where
  toFun p := p.1.toOriented p.2 x.2
  invFun p := ⟨o.forgetWalk p, o.followsOrientation_forgetWalk p⟩
  left_inv p := Subtype.ext (Walk.forgetWalk_toOriented p.1 p.2 x.2)
  right_inv := Walk.toOriented_forgetWalk

@[simp]
theorem walkEquiv_apply (o : G.Orientation) {x y : V(G)}
    (p : {p : G.Walk x y // p.FollowsOrientation o}) :
    o.walkEquiv x y p = p.1.toOriented p.2 x.2 := (rfl)

@[simp]
theorem walkEquiv_symm_apply_val (o : G.Orientation) {x y : V(G)} (p : ArrowWalk o.Hom x y) :
    ((o.walkEquiv x y).symm p).1 = o.forgetWalk p := (rfl)

/-- Directed reachability is witnessed by a native walk following the chosen directions. -/
theorem nonempty_arrowWalk_iff (o : G.Orientation) (x y : V(G)) :
    Nonempty (ArrowWalk o.Hom x y) ↔ ∃ p : G.Walk x y, p.FollowsOrientation o := by
  rw [← (o.walkEquiv x y).nonempty_congr]
  exact nonempty_subtype

end Orientation

end Graph
