/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Basic

/-!
# Isomorphisms of multigraphs

An isomorphism between Mathlib multigraphs consists of equivalences between their actual vertex
and edge types which preserve the link relation. Edge identities are part of the data, so this
notion distinguishes parallel edges and retains loops.

This file supplies identity, inverse, composition, and the groupoid laws for multigraph
isomorphisms.

## Main definitions

* `Graph.Iso`: an isomorphism of multigraphs on possibly different ambient types.
-/

public section

universe u v u' v' u'' v''

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {α'' : Type u''} {β'' : Type v''}
variable {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

/-- An isomorphism of multigraphs is an equivalence of their actual vertices and actual edges
which preserves the link relation. -/
@[ext]
structure Iso (G : Graph α β) (H : Graph α' β') where
  /-- The equivalence between actual vertices. -/
  vertexEquiv : G.vertexSet ≃ H.vertexSet
  /-- The equivalence between actual edge identities. -/
  edgeEquiv : G.edgeSet ≃ H.edgeSet
  /-- Corresponding edges link corresponding vertices. -/
  map_isLink_iff : ∀ (e : G.edgeSet) (x y : G.vertexSet),
    H.IsLink (edgeEquiv e) (vertexEquiv x) (vertexEquiv y) ↔ G.IsLink e x y

namespace Iso

attribute [simp] map_isLink_iff

/-- The identity isomorphism of a multigraph. -/
@[refl]
def refl (G : Graph α β) : Iso G G where
  vertexEquiv := Equiv.refl G.vertexSet
  edgeEquiv := Equiv.refl G.edgeSet
  map_isLink_iff _ _ _ := Iff.rfl

/-- The composite of two multigraph isomorphisms. -/
@[trans]
def trans (f : Iso G H) (g : Iso H K) : Iso G K where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  edgeEquiv := f.edgeEquiv.trans g.edgeEquiv
  map_isLink_iff e x y := (g.map_isLink_iff (f.edgeEquiv e)
    (f.vertexEquiv x) (f.vertexEquiv y)).trans (f.map_isLink_iff e x y)

/-- The inverse of a multigraph isomorphism. -/
@[symm]
def symm (f : Iso G H) : Iso H G where
  vertexEquiv := f.vertexEquiv.symm
  edgeEquiv := f.edgeEquiv.symm
  map_isLink_iff e x y := by
    rw [← f.map_isLink_iff (f.edgeEquiv.symm e) (f.vertexEquiv.symm x)
      (f.vertexEquiv.symm y)]
    simp

/-- The identity isomorphism fixes actual vertices. -/
@[simp]
theorem refl_vertexEquiv_apply (G : Graph α β) (x : G.vertexSet) :
    (refl G).vertexEquiv x = x :=
  (rfl)

/-- The identity isomorphism fixes actual edges. -/
@[simp]
theorem refl_edgeEquiv_apply (G : Graph α β) (e : G.edgeSet) :
    (refl G).edgeEquiv e = e :=
  (rfl)

/-- A composite isomorphism applies the two vertex equivalences in order. -/
@[simp]
theorem trans_vertexEquiv_apply (f : Iso G H) (g : Iso H K) (x : G.vertexSet) :
    (f.trans g).vertexEquiv x = g.vertexEquiv (f.vertexEquiv x) :=
  (rfl)

/-- A composite isomorphism applies the two edge equivalences in order. -/
@[simp]
theorem trans_edgeEquiv_apply (f : Iso G H) (g : Iso H K) (e : G.edgeSet) :
    (f.trans g).edgeEquiv e = g.edgeEquiv (f.edgeEquiv e) :=
  (rfl)

/-- The inverse isomorphism applies the inverse vertex equivalence. -/
@[simp]
theorem symm_vertexEquiv_apply (f : Iso G H) (x : H.vertexSet) :
    f.symm.vertexEquiv x = f.vertexEquiv.symm x :=
  (rfl)

/-- The inverse isomorphism applies the inverse edge equivalence. -/
@[simp]
theorem symm_edgeEquiv_apply (f : Iso G H) (e : H.edgeSet) :
    f.symm.edgeEquiv e = f.edgeEquiv.symm e :=
  (rfl)

/-- Applying an isomorphism and then its inverse fixes an actual vertex. -/
theorem symm_vertexEquiv_apply_vertexEquiv (f : Iso G H) (x : G.vertexSet) :
    f.symm.vertexEquiv (f.vertexEquiv x) = x := by
  rw [symm_vertexEquiv_apply, Equiv.symm_apply_apply]

/-- Applying an inverse isomorphism and then the original fixes an actual vertex. -/
theorem vertexEquiv_apply_symm_vertexEquiv (f : Iso G H) (x : H.vertexSet) :
    f.vertexEquiv (f.symm.vertexEquiv x) = x := by
  rw [symm_vertexEquiv_apply, Equiv.apply_symm_apply]

/-- Applying an isomorphism and then its inverse fixes an actual edge. -/
theorem symm_edgeEquiv_apply_edgeEquiv (f : Iso G H) (e : G.edgeSet) :
    f.symm.edgeEquiv (f.edgeEquiv e) = e := by
  rw [symm_edgeEquiv_apply, Equiv.symm_apply_apply]

/-- Applying an inverse isomorphism and then the original fixes an actual edge. -/
theorem edgeEquiv_apply_symm_edgeEquiv (f : Iso G H) (e : H.edgeSet) :
    f.edgeEquiv (f.symm.edgeEquiv e) = e := by
  rw [symm_edgeEquiv_apply, Equiv.apply_symm_apply]

/-- Inverting a graph isomorphism twice returns the original isomorphism. -/
@[simp]
theorem symm_symm (f : Iso G H) : f.symm.symm = f := by
  ext <;> rfl

/-- The identity graph isomorphism is self-inverse. -/
@[simp]
theorem refl_symm (G : Graph α β) : (refl G).symm = refl G := by
  rfl

/-- Composing the identity isomorphism on the left changes nothing. -/
@[simp]
theorem refl_trans (f : Iso G H) : (refl G).trans f = f := by
  ext <;> rfl

/-- Composing the identity isomorphism on the right changes nothing. -/
@[simp]
theorem trans_refl (f : Iso G H) : f.trans (refl H) = f := by
  ext <;> rfl

/-- Composition of graph isomorphisms is associative. -/
@[simp]
theorem trans_assoc (f : Iso G H) (g : Iso H K)
    {α''' β''' : Type*} {L : Graph α''' β'''} (h : Iso K L) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext <;> rfl

/-- Composing a graph isomorphism with its inverse gives the identity. -/
@[simp]
theorem self_trans_symm (f : Iso G H) : f.trans f.symm = refl G := by
  ext <;> simp

/-- Composing the inverse of a graph isomorphism with it gives the identity. -/
@[simp]
theorem symm_trans_self (f : Iso G H) : f.symm.trans f = refl H := by
  ext <;> simp

/-- A graph isomorphism sends a link to a link. -/
theorem map_isLink (f : Iso G H) {e : β} {x y : α} (he : G.IsLink e x y) :
    H.IsLink (f.edgeEquiv ⟨e, he.edge_mem⟩) (f.vertexEquiv ⟨x, he.left_mem⟩)
      (f.vertexEquiv ⟨y, he.right_mem⟩) :=
  (f.map_isLink_iff ⟨e, he.edge_mem⟩ ⟨x, he.left_mem⟩ ⟨y, he.right_mem⟩).2 he

end Iso

end Graph
