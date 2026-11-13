/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Subdividing an edge of a Serre graph

Subdividing the geometric edge of a dart `a` of a Serre graph `Γ` inserts a new vertex in the
middle of that edge: the dart `a` is replaced by a path of two darts through the new vertex, and
its reverse by the reverse path. This is the one-dimensional cutting of Seifert and Threlfall,
the operation (P1) of Gallier and Xu.

The subdivided graph `Γ.subdivide a` has vertices `Option Γ.V`, with `none` the new vertex, and
darts `Γ.E ⊕ Bool`. Every dart `e` of `Γ` keeps its initial half `Sum.inl e`, which starts at the
source of `e`: for `e` other than `a` and its reverse this is all of `e`, while `Sum.inl a` and
`Sum.inl (rev a)` end at the new vertex. The two darts starting at the new vertex are
`Sum.inr true`, ending at the target of `a`, and `Sum.inr false`, ending at the source of `a`. So
the darts starting at an old vertex are unchanged, and each dart `e` of `Γ` is replaced by a path
starting with `Sum.inl e` and ending with `Γ.subdivideLast a e`.

## Main definitions

* `TauCeti.SerreGraph.subdivide`: the graph obtained by subdividing an edge.
* `TauCeti.SerreGraph.subdivideRev`: its reversal, the form in which `simp` states the reversal
  of the subdivided graph.
* `TauCeti.SerreGraph.subdivideLast`: the last dart of the path replacing a dart.
* `TauCeti.SerreGraph.subdivideOrigin`: the dart on which a dart of the subdivided graph lies.
* `TauCeti.SerreGraph.subdivideGeomEdgeEquiv`: the geometric edges of the subdivided graph are
  those of the original graph and one more.

## Main results

* `TauCeti.SerreGraph.connected_subdivide_iff`: a graph is connected exactly when its
  subdivision is.
* `TauCeti.SerreGraph.card_subdivide_V`, `TauCeti.SerreGraph.card_subdivide_geomEdge`: a subdivision
  has one more vertex and one more geometric edge.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definition 6.3, operation (P1).
-/

public section

universe u v

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph.{u, v}) [DecidableEq Γ.E] (a : Γ.E)

/-- The reversal of the darts of `Γ.subdivide a`: the initial halves of `a` and of its reverse are
the reverses of the darts from the new vertex to the source and to the target of `a`, and the
other darts are reversed as in `Γ`. -/
def subdivideRev : Γ.E ⊕ Bool → Γ.E ⊕ Bool :=
  Sum.elim
    (fun e => if e = a then .inr false else if e = Γ.rev a then .inr true else .inl (Γ.rev e))
    fun b => .inl (cond b (Γ.rev a) a)

variable {Γ} in
@[simp] theorem subdivideRev_inl_self : Γ.subdivideRev a (.inl a) = .inr false := by
  simp [subdivideRev]

variable {Γ} in
@[simp] theorem subdivideRev_inl_rev : Γ.subdivideRev a (.inl (Γ.rev a)) = .inr true := by
  simp [subdivideRev, Γ.rev_ne a]

variable {Γ a} in
/-- A dart other than `a` and its reverse is reversed as in the original graph. -/
theorem subdivideRev_inl_of_ne {e : Γ.E} (h : e ≠ a) (h' : e ≠ Γ.rev a) :
    Γ.subdivideRev a (.inl e) = .inl (Γ.rev e) := by
  simp [subdivideRev, h, h']

variable {Γ} in
@[simp] theorem subdivideRev_inr (b : Bool) :
    Γ.subdivideRev a (.inr b) = .inl (cond b (Γ.rev a) a) := (rfl)

variable {Γ} in
@[simp] theorem subdivideRev_subdivideRev (x : Γ.E ⊕ Bool) :
    Γ.subdivideRev a (Γ.subdivideRev a x) = x := by
  obtain e | _ | _ := x
  · by_cases h : e = a
    · simp [h]
    · by_cases h' : e = Γ.rev a
      · simp [h']
      · rw [subdivideRev_inl_of_ne h h', subdivideRev_inl_of_ne
          (fun hr => h' (by rw [← hr, Γ.rev_rev])) (Γ.rev_injective.ne h), Γ.rev_rev]
  · simp
  · simp

variable {Γ} in
theorem subdivideRev_ne (x : Γ.E ⊕ Bool) : Γ.subdivideRev a x ≠ x := by
  obtain e | _ | _ := x
  · by_cases h : e = a
    · simp [h]
    · by_cases h' : e = Γ.rev a
      · simp [h']
      · simp [subdivideRev_inl_of_ne h h', Γ.rev_ne e]
  · simp
  · simp

/-- The Serre graph obtained from `Γ` by subdividing the geometric edge of the dart `a`. Its new
vertex is `none`. The dart `Sum.inl e` is the initial half of `e`: all of `e` when `e` is neither
`a` nor its reverse, and otherwise the half of `e` ending at the new vertex. The darts
`Sum.inr true` and `Sum.inr false` run from the new vertex to the target and to the source of `a`.
It is reducible, so that its vertices and darts are seen to be `Option Γ.V` and `Γ.E ⊕ Bool`. -/
abbrev subdivide : SerreGraph.{u, v} where
  V := Option Γ.V
  E := Γ.E ⊕ Bool
  src := Sum.elim (fun e => some (Γ.src e)) fun _ => none
  rev := Γ.subdivideRev a
  rev_rev := subdivideRev_subdivideRev a
  rev_ne := subdivideRev_ne a

variable {Γ}

@[simp] theorem subdivide_src_inl (e : Γ.E) :
    (Γ.subdivide a).src (.inl e) = some (Γ.src e) := (rfl)

@[simp] theorem subdivide_src_inr (b : Bool) : (Γ.subdivide a).src (.inr b) = none := (rfl)

/-- The reversal of `Γ.subdivide a` is `Γ.subdivideRev a`. -/
theorem subdivide_rev (x : (Γ.subdivide a).E) : (Γ.subdivide a).rev x = Γ.subdivideRev a x := (rfl)

/-- The initial half of `a` ends at the new vertex. -/
@[simp] theorem subdivide_tgt_inl_self : (Γ.subdivide a).tgt (.inl a) = none := by
  rw [tgt_def, subdivide_rev, subdivideRev_inl_self, subdivide_src_inr]

/-- The initial half of the reverse of `a` ends at the new vertex. -/
@[simp] theorem subdivide_tgt_inl_rev : (Γ.subdivide a).tgt (.inl (Γ.rev a)) = none := by
  rw [tgt_def, subdivide_rev, subdivideRev_inl_rev, subdivide_src_inr]

variable {a} in
/-- A dart other than `a` and its reverse keeps its target. -/
theorem subdivide_tgt_inl_of_ne {e : Γ.E} (h : e ≠ a) (h' : e ≠ Γ.rev a) :
    (Γ.subdivide a).tgt (.inl e) = some (Γ.tgt e) := by
  rw [tgt_def, subdivide_rev, subdivideRev_inl_of_ne h h', subdivide_src_inl, src_rev]

@[simp] theorem subdivide_tgt_inr_true : (Γ.subdivide a).tgt (.inr true) = some (Γ.tgt a) := by
  rw [tgt_def, subdivide_rev, subdivideRev_inr, subdivide_src_inl]
  exact congrArg some (Γ.src_rev a)

@[simp] theorem subdivide_tgt_inr_false : (Γ.subdivide a).tgt (.inr false) = some (Γ.src a) := by
  rw [tgt_def, subdivide_rev, subdivideRev_inr, subdivide_src_inl]
  rfl

/-! ### The path replacing a dart -/

variable (Γ) in
/-- The last dart of the path of `Γ.subdivide a` replacing the dart `e` of `Γ`: the dart from the
new vertex to the target of `e` when `e` is `a` or its reverse, and `Sum.inl e` otherwise. The
first dart of that path is `Sum.inl e`. -/
def subdivideLast (e : Γ.E) : (Γ.subdivide a).E :=
  if e = a ∨ e = Γ.rev a then .inr (decide (e = a)) else .inl e

variable {a} in
theorem subdivideLast_of_eq_or_eq {e : Γ.E} (h : e = a ∨ e = Γ.rev a) :
    Γ.subdivideLast a e = .inr (decide (e = a)) := by
  simp [subdivideLast, h]

variable {a} in
theorem subdivideLast_of_ne {e : Γ.E} (h : e ≠ a) (h' : e ≠ Γ.rev a) :
    Γ.subdivideLast a e = .inl e := by
  simp [subdivideLast, h, h']

@[simp] theorem subdivideLast_self : Γ.subdivideLast a a = .inr true := by
  simp [subdivideLast]

@[simp] theorem subdivideLast_rev : Γ.subdivideLast a (Γ.rev a) = .inr false := by
  simp [subdivideLast, Γ.rev_ne a]

/-- The path replacing the reverse of `e` starts with the reverse of the last dart of the path
replacing `e`. -/
@[simp] theorem subdivideRev_subdivideLast (e : Γ.E) :
    Γ.subdivideRev a (Γ.subdivideLast a e) = .inl (Γ.rev e) := by
  by_cases h : e = a
  · simp [h]
  · by_cases h' : e = Γ.rev a
    · simp [h']
    · rw [subdivideLast_of_ne h h', subdivideRev_inl_of_ne h h']

/-- The path replacing `e` ends at the target of `e`. -/
@[simp] theorem subdivide_tgt_subdivideLast (e : Γ.E) :
    (Γ.subdivide a).tgt (Γ.subdivideLast a e) = some (Γ.tgt e) := by
  rw [tgt_def, subdivide_rev, subdivideRev_subdivideLast, subdivide_src_inl, src_rev]

variable (Γ) in
/-- The dart of `Γ` on which a dart of `Γ.subdivide a` lies: `Sum.inl e` lies on `e`, and the
darts from the new vertex to the target and to the source of `a` lie on `a` and on its reverse. -/
def subdivideOrigin : (Γ.subdivide a).E → Γ.E := Sum.elim id fun b => cond b a (Γ.rev a)

@[simp] theorem subdivideOrigin_inl (e : Γ.E) : Γ.subdivideOrigin a (.inl e) = e := (rfl)

@[simp] theorem subdivideOrigin_inr (b : Bool) :
    Γ.subdivideOrigin a (.inr b) = cond b a (Γ.rev a) := (rfl)

/-- Reversing a dart of the subdivision reverses the dart on which it lies. -/
@[simp] theorem subdivideOrigin_subdivideRev (x : (Γ.subdivide a).E) :
    Γ.subdivideOrigin a (Γ.subdivideRev a x) = Γ.rev (Γ.subdivideOrigin a x) := by
  obtain e | _ | _ := x
  · by_cases h : e = a
    · simp [h]
    · by_cases h' : e = Γ.rev a
      · simp [h']
      · simp [subdivideRev_inl_of_ne h h']
  · simp
  · simp

/-- The last dart of the path replacing `e` lies on `e`. -/
@[simp] theorem subdivideOrigin_subdivideLast (e : Γ.E) :
    Γ.subdivideOrigin a (Γ.subdivideLast a e) = e := by
  by_cases h : e = a
  · simp [h]
  · by_cases h' : e = Γ.rev a
    · simp [h']
    · simp [subdivideLast_of_ne h h']

/-- When `e` is `a` or its reverse, the path replacing `e` passes through the new vertex. -/
theorem subdivide_tgt_inl_of_eq_or_eq {e : Γ.E} (h : e = a ∨ e = Γ.rev a) :
    (Γ.subdivide a).tgt (.inl e) = none := by
  rcases h with rfl | rfl <;> simp

/-- Every dart of `Γ` is replaced by a path of `Γ.subdivide a` with the same endpoints. -/
theorem nonempty_subdivide_path_dart (e : Γ.E) :
    Nonempty ((Γ.subdivide a).Path (some (Γ.src e)) (some (Γ.tgt e))) := by
  -- The vertex type of the subdivision reduces to `Option Γ.V`, which hides its quiver structure.
  let := (Γ.subdivide a).toQuiver
  by_cases h : e = a ∨ e = Γ.rev a
  · exact ⟨(Quiver.Hom.toPath (⟨.inl e, rfl, subdivide_tgt_inl_of_eq_or_eq a h⟩ :
      Quiver.Hom (V := (Γ.subdivide a).V) _ none)).cons
        ⟨Γ.subdivideLast a e, by rw [subdivideLast_of_eq_or_eq h, subdivide_src_inr],
          subdivide_tgt_subdivideLast a e⟩⟩
  · rw [not_or] at h
    exact ⟨Quiver.Hom.toPath ⟨.inl e, rfl, subdivide_tgt_inl_of_ne h.1 h.2⟩⟩

/-- Every path of `Γ` is replaced by a path of `Γ.subdivide a` with the same endpoints. -/
theorem nonempty_subdivide_path {x y : Γ.V} (p : Γ.Path x y) :
    Nonempty ((Γ.subdivide a).Path (some x) (some y)) := by
  -- The vertex type of the subdivision reduces to `Option Γ.V`, which hides its quiver structure.
  let := (Γ.subdivide a).toQuiver
  induction p with
  | nil => exact ⟨.nil⟩
  | cons _ e ih =>
    obtain ⟨q⟩ := ih
    obtain ⟨r⟩ := nonempty_subdivide_path_dart a e.1
    rw [e.2.1, e.2.2] at r
    exact ⟨q.comp r⟩

/-- Subdividing an edge of a connected graph gives a connected graph. -/
theorem Connected.subdivide (h : Γ.Connected) : (Γ.subdivide a).Connected := by
  -- The vertex type of the subdivision reduces to `Option Γ.V`, which hides its quiver structure.
  let := (Γ.subdivide a).toQuiver
  obtain ⟨⟨x⟩, hpre⟩ := Γ.connected_iff.1 h
  refine (connected_iff _).2 ⟨⟨some x⟩, preconnected_of_forall_nonempty_path _ (some x) ?_⟩
  rintro (_ | y)
  · obtain ⟨p⟩ := nonempty_subdivide_path a ((Γ.preconnected_iff.1 hpre x (Γ.src a)).some)
    exact ⟨p.cons ⟨.inl a, rfl, subdivide_tgt_inl_self a⟩⟩
  · exact nonempty_subdivide_path a (Γ.preconnected_iff.1 hpre x y).some

/-- The step of the contraction of the subdivided edge onto the source of `a`: the endpoints of a
dart of `Γ.subdivide a`, the new vertex sent to the source of `a`, are joined by a path of `Γ`. -/
private theorem nonempty_path_getD_dart (x : (Γ.subdivide a).E) :
    Nonempty (Γ.Path (((Γ.subdivide a).src x).getD (Γ.src a))
      (((Γ.subdivide a).tgt x).getD (Γ.src a))) := by
  obtain e | _ | _ := x
  · by_cases h : e = a
    · subst h
      exact ⟨by simpa using (Quiver.Path.nil : Γ.Path (Γ.src e) (Γ.src e))⟩
    · by_cases h' : e = Γ.rev a
      · subst h'
        simpa using Nonempty.intro (Quiver.Hom.toPath (Γ.dart (Γ.rev a)))
      · rw [subdivide_tgt_inl_of_ne h h']
        exact ⟨Quiver.Hom.toPath (Γ.dart e)⟩
  · exact ⟨by simpa using (Quiver.Path.nil : Γ.Path (Γ.src a) (Γ.src a))⟩
  · simpa using Nonempty.intro (Quiver.Hom.toPath (Γ.dart a))

/-- Contracting the subdivided edge onto the source of `a` turns a path of `Γ.subdivide a` into a
path of `Γ`. -/
private theorem nonempty_path_getD {x y : (Γ.subdivide a).V} (p : (Γ.subdivide a).Path x y) :
    Nonempty (Γ.Path (x.getD (Γ.src a)) (y.getD (Γ.src a))) := by
  -- The vertex type of the subdivision reduces to `Option Γ.V`, which hides its quiver structure.
  let := (Γ.subdivide a).toQuiver
  induction p with
  | nil => exact ⟨.nil⟩
  | cons _ e ih =>
    obtain ⟨q⟩ := ih
    obtain ⟨r⟩ := nonempty_path_getD_dart a e.1
    rw [e.2.1, e.2.2] at r
    exact ⟨q.comp r⟩

/-- A graph is connected exactly when the graph obtained by subdividing one of its edges is. -/
@[simp] theorem connected_subdivide_iff : (Γ.subdivide a).Connected ↔ Γ.Connected :=
  ⟨fun h => (connected_iff _).2 ⟨⟨Γ.src a⟩, (preconnected_iff _).2 fun x y =>
    nonempty_path_getD a ((preconnected_iff _).1 ((connected_iff _).1 h).2 (some x)
      (some y)).some⟩,
    Connected.subdivide a⟩

/-! ### Counting vertices and edges -/

/-- A subdivision has one more vertex. -/
theorem card_subdivide_V [Finite Γ.V] : Nat.card (Γ.subdivide a).V = Nat.card Γ.V + 1 :=
  Finite.card_option

/-- The two darts of the half of the subdivided edge at the source of `a` have the same geometric
edge. -/
theorem toGeomEdge_subdivide_inr_false :
    (Γ.subdivide a).toGeomEdge (.inr false) = (Γ.subdivide a).toGeomEdge (.inl a) :=
  ((Γ.subdivide a).toGeomEdge_rev (.inr false)).symm

/-- The two darts of the half of the subdivided edge at the target of `a` have the same geometric
edge. -/
theorem toGeomEdge_subdivide_inr_true :
    (Γ.subdivide a).toGeomEdge (.inr true) = (Γ.subdivide a).toGeomEdge (.inl (Γ.rev a)) :=
  ((Γ.subdivide a).toGeomEdge_rev (.inr true)).symm

variable {a} in
/-- Away from the subdivided edge, the initial halves of a dart and of its reverse have the same
geometric edge. -/
theorem toGeomEdge_subdivide_inl_rev_of_ne {e : Γ.E} (h : e ≠ a) (h' : e ≠ Γ.rev a) :
    (Γ.subdivide a).toGeomEdge (.inl (Γ.rev e)) = (Γ.subdivide a).toGeomEdge (.inl e) := by
  rw [← subdivideRev_inl_of_ne h h']
  exact (Γ.subdivide a).toGeomEdge_rev (.inl e)

/-- The geometric edge of `Γ`, or the new geometric edge `none`, named by a dart of the
subdivision. -/
private def subdivideGeomEdgeFun : (Γ.subdivide a).E → Option Γ.GeomEdge :=
  Sum.elim (fun e => if e = a then none else some (Γ.toGeomEdge e))
    fun b => cond b (some (Γ.toGeomEdge a)) none

private theorem subdivideGeomEdgeFun_subdivideRev (x : (Γ.subdivide a).E) :
    subdivideGeomEdgeFun a (Γ.subdivideRev a x) = subdivideGeomEdgeFun a x := by
  obtain e | _ | _ := x
  · by_cases h : e = a
    · simp [subdivideGeomEdgeFun, h]
    · by_cases h' : e = Γ.rev a
      · simp [subdivideGeomEdgeFun, h', Γ.rev_ne a]
      · simp [subdivideGeomEdgeFun, subdivideRev_inl_of_ne h h', h, h',
          ← Γ.rev_injective.eq_iff (a := Γ.rev e)]
  · simp [subdivideGeomEdgeFun]
  · simp [subdivideGeomEdgeFun, Γ.rev_ne a]

/-- The geometric edge of the subdivision lying on a dart of `Γ` and keeping its name: the half of
the subdivided edge at the target of `a` for `a`, and the initial half of `e` for any other `e`. -/
private def subdivideGeomEdgeInv (e : Γ.E) : (Γ.subdivide a).GeomEdge :=
  (Γ.subdivide a).toGeomEdge (if e = a then .inr true else .inl e)

private theorem subdivideGeomEdgeInv_rev (e : Γ.E) :
    subdivideGeomEdgeInv a (Γ.rev e) = subdivideGeomEdgeInv a e := by
  by_cases h : e = a
  · simpa [subdivideGeomEdgeInv, h, Γ.rev_ne a] using (toGeomEdge_subdivide_inr_true a).symm
  · by_cases h' : e = Γ.rev a
    · simpa [subdivideGeomEdgeInv, h', Γ.rev_ne a] using toGeomEdge_subdivide_inr_true a
    · have hr : Γ.rev e ≠ a := fun hr => h' (by rw [← hr, Γ.rev_rev])
      simpa [subdivideGeomEdgeInv, h, hr] using toGeomEdge_subdivide_inl_rev_of_ne h h'

variable (Γ) in
/-- The geometric edges of a subdivision are the geometric edges of the original graph and one
more: `none` is the half of the subdivided edge at the source of `a`, and the other half keeps
the name of the subdivided edge. -/
def subdivideGeomEdgeEquiv : (Γ.subdivide a).GeomEdge ≃ Option Γ.GeomEdge where
  toFun := GeomEdge.lift _ (subdivideGeomEdgeFun a) (subdivideGeomEdgeFun_subdivideRev a)
  invFun x := x.elim ((Γ.subdivide a).toGeomEdge (.inl a)) <|
    GeomEdge.lift _ (subdivideGeomEdgeInv a) (subdivideGeomEdgeInv_rev a)
  left_inv x := by
    obtain ⟨e | _ | _, rfl⟩ := (Γ.subdivide a).toGeomEdge_surjective x
    · by_cases h : e = a
      · simp [subdivideGeomEdgeFun, h]
      · simp [subdivideGeomEdgeFun, subdivideGeomEdgeInv, h]
    · simpa [subdivideGeomEdgeFun] using (toGeomEdge_subdivide_inr_false a).symm
    · simp [subdivideGeomEdgeFun, subdivideGeomEdgeInv]
  right_inv x := by
    obtain _ | x := x
    · simp [subdivideGeomEdgeFun]
    · obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective x
      by_cases h : e = a <;> simp [subdivideGeomEdgeFun, subdivideGeomEdgeInv, h]

/-- The initial half of `a` lies on the new geometric edge, and the initial half of any other dart
on the geometric edge of that dart. -/
@[simp] theorem subdivideGeomEdgeEquiv_toGeomEdge_inl (e : Γ.E) :
    Γ.subdivideGeomEdgeEquiv a ((Γ.subdivide a).toGeomEdge (.inl e)) =
      if e = a then none else some (Γ.toGeomEdge e) := by
  simp [subdivideGeomEdgeEquiv, subdivideGeomEdgeFun]

/-- The half of the subdivided edge at the target of `a` keeps the name of the subdivided edge, and
the half at its source is the new geometric edge. -/
@[simp] theorem subdivideGeomEdgeEquiv_toGeomEdge_inr (b : Bool) :
    Γ.subdivideGeomEdgeEquiv a ((Γ.subdivide a).toGeomEdge (.inr b)) =
      cond b (some (Γ.toGeomEdge a)) none := by
  simp [subdivideGeomEdgeEquiv, subdivideGeomEdgeFun]

/-- The new geometric edge is the half of the subdivided edge at the source of `a`. -/
@[simp] theorem subdivideGeomEdgeEquiv_symm_none :
    (Γ.subdivideGeomEdgeEquiv a).symm none = (Γ.subdivide a).toGeomEdge (.inl a) := (rfl)

/-- The geometric edge of `a` names the half of the subdivided edge at the target of `a`, and the
geometric edge of any other dart names the edge of its initial half. -/
@[simp] theorem subdivideGeomEdgeEquiv_symm_some_toGeomEdge (e : Γ.E) :
    (Γ.subdivideGeomEdgeEquiv a).symm (some (Γ.toGeomEdge e)) =
      (Γ.subdivide a).toGeomEdge (if e = a then .inr true else .inl e) := by
  simp only [subdivideGeomEdgeEquiv, Equiv.coe_fn_symm_mk, Option.elim_some,
    GeomEdge.lift_toGeomEdge, subdivideGeomEdgeInv]

/-- A subdivision of a graph with finitely many geometric edges has finitely many geometric
edges. -/
instance [Finite Γ.GeomEdge] : Finite (Γ.subdivide a).GeomEdge :=
  .of_equiv _ (Γ.subdivideGeomEdgeEquiv a).symm

/-- A subdivision has one more geometric edge. -/
@[simp] theorem card_subdivide_geomEdge [Finite Γ.GeomEdge] :
    Nat.card (Γ.subdivide a).GeomEdge = Nat.card Γ.GeomEdge + 1 := by
  rw [Nat.card_congr (Γ.subdivideGeomEdgeEquiv a), Finite.card_option]

end SerreGraph

end TauCeti
