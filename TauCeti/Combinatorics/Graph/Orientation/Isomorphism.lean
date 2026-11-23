/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Isomorphism.Basic
public import TauCeti.Combinatorics.Graph.Orientation.Indegree

/-!
# Transport of multigraph orientations under isomorphisms

A graph isomorphism transports the chosen tail and head of each actual edge. This gives an
equivalence of orientations, commuting with composition and reversal. Parallel edges retain
their separate directions and loops retain their unique direction.

With finitely many actual edges, transport preserves indegrees and outdegrees at corresponding
vertices. In particular, existence of an orientation with prescribed or bounded indegrees is
invariant under graph isomorphisms. No finiteness of the vertex sets or ambient types is needed.
-/

public section

open Finset

namespace Graph.Iso

universe u v u' v' u'' v''

variable {V : Type u} {E : Type v} {V' : Type u'} {E' : Type v'}
  {V'' : Type u''} {E'' : Type v''}
  {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}

/-- A graph isomorphism identifies orientations by transporting the ordered ends of every edge. -/
def orientationEquiv (f : Iso G H) : G.Orientation ≃ H.Orientation where
  toFun o :=
    { tail e := f.vertexEquiv (o.tail (f.edgeEquiv.symm e))
      head e := f.vertexEquiv (o.head (f.edgeEquiv.symm e))
      isLink e := by
        simpa using (f.map_isLink_iff _ _ _).2 (o.isLink (f.edgeEquiv.symm e)) }
  invFun o :=
    { tail e := f.vertexEquiv.symm (o.tail (f.edgeEquiv e))
      head e := f.vertexEquiv.symm (o.head (f.edgeEquiv e))
      isLink e := by
        simpa using (f.symm.map_isLink_iff _ _ _).2 (o.isLink (f.edgeEquiv e)) }
  left_inv o := Orientation.ext_of_head fun e ↦ by simp
  right_inv o := Orientation.ext_of_head fun e ↦ by simp

/-- The tail of a transported edge is the transported tail. -/
@[simp]
theorem orientationEquiv_tail (f : Iso G H) (o : G.Orientation) (e : H.edgeSet) :
    (f.orientationEquiv o).tail e = f.vertexEquiv (o.tail (f.edgeEquiv.symm e)) := (rfl)

/-- The head of a transported edge is the transported head. -/
@[simp]
theorem orientationEquiv_head (f : Iso G H) (o : G.Orientation) (e : H.edgeSet) :
    (f.orientationEquiv o).head e = f.vertexEquiv (o.head (f.edgeEquiv.symm e)) := (rfl)

/-- Transport by the inverse graph isomorphism is inverse transport of orientations. -/
@[simp]
theorem orientationEquiv_symm (f : Iso G H) :
    f.orientationEquiv.symm = f.symm.orientationEquiv := by
  apply Equiv.ext
  intro o
  rw [Equiv.symm_apply_eq]
  exact Orientation.ext_of_head fun _ ↦ by simp

/-- The identity graph isomorphism acts trivially on orientations. -/
@[simp]
theorem orientationEquiv_refl (G : Graph V E) :
    (Iso.refl G).orientationEquiv = Equiv.refl G.Orientation := by
  apply Equiv.ext
  intro o
  exact Orientation.ext_of_head fun _ ↦ by simp

/-- Transport of orientations respects composition of graph isomorphisms. -/
@[simp]
theorem orientationEquiv_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).orientationEquiv = f.orientationEquiv.trans g.orientationEquiv := by
  apply Equiv.ext
  intro o
  apply Orientation.ext_of_head
  intro e
  simp

/-- Reversing every edge commutes with transporting an orientation. -/
@[simp]
theorem orientationEquiv_reverse (f : Iso G H) (o : G.Orientation) :
    f.orientationEquiv o.reverse = (f.orientationEquiv o).reverse := by
  exact Orientation.ext_of_head fun _ ↦ by simp

section Degree

variable [Fintype G.edgeSet] [Fintype H.edgeSet]

/-- Corresponding vertices have the same indegree in corresponding orientations. -/
@[simp]
theorem indegree_orientationEquiv (f : Iso G H) (o : G.Orientation) (x : H.vertexSet) :
    (f.orientationEquiv o).indegree x = o.indegree (f.vertexEquiv.symm x) := by
  classical
  rw [Orientation.indegree_def, Orientation.indegree_def]
  apply card_equiv f.edgeEquiv.symm
  intro e
  simp [← Equiv.eq_symm_apply]

/-- Corresponding vertices have the same outdegree in corresponding orientations. -/
@[simp]
theorem outdegree_orientationEquiv (f : Iso G H) (o : G.Orientation) (x : H.vertexSet) :
    (f.orientationEquiv o).outdegree x = o.outdegree (f.vertexEquiv.symm x) := by
  simpa using f.indegree_orientationEquiv o.reverse x

/-- Existence of an orientation satisfying any predicate on its indegree function is invariant
under graph isomorphisms, with target indegrees indexed by the original vertices. -/
theorem exists_orientation_indegree_congr (f : Iso G H) (P : (G.vertexSet → ℕ) → Prop) :
    (∃ o : H.Orientation, P (fun x ↦ o.indegree (f.vertexEquiv x))) ↔
      ∃ o : G.Orientation, P o.indegree := by
  exact (f.orientationEquiv.exists_congr fun o ↦ by simp).symm

/-- Prescribed indegrees are realizable exactly when the transported prescription is realizable.
The vertex and edge equivalences, rather than the ambient types, determine the transport. -/
theorem exists_orientation_indegree_eq_congr (f : Iso G H) (d : G.vertexSet → ℕ) :
    (∃ o : H.Orientation, ∀ x, o.indegree x = d (f.vertexEquiv.symm x)) ↔
      ∃ o : G.Orientation, ∀ x, o.indegree x = d x := by
  simpa only [f.vertexEquiv.forall_congr_left, Equiv.apply_symm_apply] using
    f.exists_orientation_indegree_congr (fun d' ↦ ∀ x, d' x = d x)

/-- Lower and upper indegree constraints are invariant under graph isomorphisms. No consistency
hypothesis on the bounds is necessary for this equivalence. -/
theorem exists_orientation_indegree_mem_Icc_congr (f : Iso G H) (a b : G.vertexSet → ℕ) :
    (∃ o : H.Orientation, ∀ x,
      o.indegree x ∈ Set.Icc (a (f.vertexEquiv.symm x)) (b (f.vertexEquiv.symm x))) ↔
      ∃ o : G.Orientation, ∀ x, o.indegree x ∈ Set.Icc (a x) (b x) := by
  simpa only [f.vertexEquiv.forall_congr_left, Equiv.apply_symm_apply] using
    f.exists_orientation_indegree_congr (fun d ↦ ∀ x, d x ∈ Set.Icc (a x) (b x))

end Degree

end Graph.Iso
