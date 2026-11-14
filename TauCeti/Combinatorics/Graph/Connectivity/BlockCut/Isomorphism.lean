/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Block
public import TauCeti.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Isomorphism

/-!
# Isomorphisms of multigraph block--cut graphs

A multigraph isomorphism induces an isomorphism of the underlying simple graphs on its actual
vertices. Consequently, it transports vertex blocks and cut vertices, and induces an
isomorphism of the corresponding block--cut incidence graphs. These constructions retain the
actual-vertex equivalence while intentionally forgetting loops and parallel-edge multiplicities,
which do not affect vertex blocks.

The transport respects identity, inverse and composition. In particular, the block--cut forest
of a multigraph can be relabelled directly along a multigraph isomorphism without choosing
representatives of blocks or cut vertices. No finiteness hypothesis is needed.
-/

public section

open Set

universe u v u' v' u'' v''

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {α'' : Type u''} {β'' : Type v''}
variable {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}

namespace Iso

/-! ### Preservation of blocks and cut vertices -/

/-- A vertex set is a block of a multigraph if and only if its image under a multigraph
isomorphism is a block. -/
@[simp]
theorem isBlock_image_iff (f : Iso G H) {B : Set V(G)} :
    H.IsBlock (f.vertexEquiv '' B) ↔ G.IsBlock B :=
  by simpa only [toSimpleGraphIso_apply] using
    (f.toSimpleGraphIso.isBlock_image_iff (B := B))

/-- A native multigraph cut vertex is carried to a native cut vertex by a multigraph
isomorphism. -/
@[simp]
theorem isCutVertex_vertexEquiv_iff (f : Iso G H) (x : V(G)) :
    H.IsCutVertex (f.vertexEquiv x) ↔ G.IsCutVertex x := by
  rw [H.isCutVertex_iff_toSimpleGraph_isCutVertex (f.vertexEquiv x).property,
    G.isCutVertex_iff_toSimpleGraph_isCutVertex x.property]
  simpa only [toSimpleGraphIso_apply] using
    (f.toSimpleGraphIso.isCutVertex_iff (v := x))

/-! ### Equivalences and the incidence graph -/

/-- The equivalence of multigraph vertex blocks induced by an isomorphism. -/
def blockEquiv (f : Iso G H) :
    {B : Set V(G) // G.IsBlock B} ≃ {B : Set V(H) // H.IsBlock B} :=
  f.toSimpleGraphIso.blockEquiv

/-- Transporting a multigraph vertex block takes its image under the vertex equivalence. -/
@[simp]
theorem coe_blockEquiv_apply (f : Iso G H) (B : {B : Set V(G) // G.IsBlock B}) :
    (f.blockEquiv B : Set V(H)) = f.vertexEquiv '' (B : Set V(G)) :=
  by simp only [blockEquiv, SimpleGraph.Iso.coe_blockEquiv_apply,
    toSimpleGraphIso_apply]

/-- Inverse transport of a multigraph vertex block takes its image under the inverse vertex
equivalence. -/
@[simp]
theorem coe_blockEquiv_symm_apply (f : Iso G H) (B : {B : Set V(H) // H.IsBlock B}) :
    (f.blockEquiv.symm B : Set V(G)) = f.vertexEquiv.symm '' (B : Set V(H)) :=
  by simp only [blockEquiv, SimpleGraph.Iso.coe_blockEquiv_symm_apply,
    toSimpleGraphIso_symm_apply]

/-- The equivalence of cut vertices of the underlying simple graphs induced by a multigraph
isomorphism. Through `Graph.isCutVertex_iff_toSimpleGraph_isCutVertex`, these are exactly the
native cut vertices among the actual vertices. -/
def cutVertexEquiv (f : Iso G H) :
    G.toSimpleGraph.CutVertex ≃ H.toSimpleGraph.CutVertex :=
  f.toSimpleGraphIso.cutVertexEquiv

/-- Transport of a cut vertex agrees with the multigraph vertex equivalence. -/
@[simp]
theorem coe_cutVertexEquiv_apply (f : Iso G H) (x : G.toSimpleGraph.CutVertex) :
    (f.cutVertexEquiv x : V(H)) = f.vertexEquiv x :=
  by simp only [cutVertexEquiv, SimpleGraph.Iso.coe_cutVertexEquiv_apply,
    toSimpleGraphIso_apply]

/-- Inverse transport of a cut vertex agrees with the inverse multigraph vertex equivalence. -/
@[simp]
theorem coe_cutVertexEquiv_symm_apply (f : Iso G H) (x : H.toSimpleGraph.CutVertex) :
    (f.cutVertexEquiv.symm x : V(G)) = f.vertexEquiv.symm x :=
  by simp only [cutVertexEquiv, SimpleGraph.Iso.coe_cutVertexEquiv_symm_apply,
    toSimpleGraphIso_symm_apply]

/-- A multigraph isomorphism induces an isomorphism between the block--cut incidence graphs of
the underlying simple graphs on actual vertices. -/
def blockCutGraphIso (f : Iso G H) :
    G.toSimpleGraph.blockCutGraph ≃g H.toSimpleGraph.blockCutGraph :=
  f.toSimpleGraphIso.blockCutGraphIso

/-- A block vertex is sent to its transported block vertex. -/
@[simp]
theorem blockCutGraphIso_apply_block (f : Iso G H)
    (B : G.toSimpleGraph.BlockVertex) :
    f.blockCutGraphIso (.inl B) = .inl (f.blockEquiv B) :=
  by simp only [blockCutGraphIso, blockEquiv,
    SimpleGraph.Iso.blockCutGraphIso_apply_block]

/-- A cut vertex is sent to its transported cut vertex. -/
@[simp]
theorem blockCutGraphIso_apply_cutVertex (f : Iso G H)
    (x : G.toSimpleGraph.CutVertex) :
    f.blockCutGraphIso (.inr x) = .inr (f.cutVertexEquiv x) :=
  by simp only [blockCutGraphIso, cutVertexEquiv,
    SimpleGraph.Iso.blockCutGraphIso_apply_cutVertex]

/-- The inverse incidence-graph map sends a block vertex back by inverse block transport. -/
@[simp]
theorem blockCutGraphIso_symm_apply_block (f : Iso G H)
    (B : H.toSimpleGraph.BlockVertex) :
    f.blockCutGraphIso.symm (.inl B) = .inl (f.blockEquiv.symm B) :=
  by simp only [blockCutGraphIso, blockEquiv,
    SimpleGraph.Iso.blockCutGraphIso_symm_apply_block]

/-- The inverse incidence-graph map sends a cut vertex back by inverse vertex transport. -/
@[simp]
theorem blockCutGraphIso_symm_apply_cutVertex (f : Iso G H)
    (x : H.toSimpleGraph.CutVertex) :
    f.blockCutGraphIso.symm (.inr x) = .inr (f.cutVertexEquiv.symm x) :=
  by simp only [blockCutGraphIso, cutVertexEquiv,
    SimpleGraph.Iso.blockCutGraphIso_symm_apply_cutVertex]

/-! ### Functoriality -/

/-- Identity multigraph isomorphisms act identically on vertex blocks. -/
@[simp]
theorem blockEquiv_refl : (refl G).blockEquiv = Equiv.refl _ := by
  rw [blockEquiv, toSimpleGraphIso_refl, SimpleGraph.Iso.blockEquiv_refl]

/-- Identity multigraph isomorphisms act identically on cut vertices. -/
@[simp]
theorem cutVertexEquiv_refl : (refl G).cutVertexEquiv = Equiv.refl _ := by
  rw [cutVertexEquiv, toSimpleGraphIso_refl, SimpleGraph.Iso.cutVertexEquiv_refl]

/-- Multigraph block transport commutes with composition. -/
@[simp]
theorem blockEquiv_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).blockEquiv = f.blockEquiv.trans g.blockEquiv := by
  simp only [blockEquiv, toSimpleGraphIso_trans, SimpleGraph.Iso.blockEquiv_comp]

/-- Multigraph cut-vertex transport commutes with composition. -/
@[simp]
theorem cutVertexEquiv_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).cutVertexEquiv = f.cutVertexEquiv.trans g.cutVertexEquiv := by
  simp only [cutVertexEquiv, toSimpleGraphIso_trans, SimpleGraph.Iso.cutVertexEquiv_comp]

/-- Transport by an inverse multigraph isomorphism is inverse block transport. -/
@[simp]
theorem blockEquiv_symm (f : Iso G H) : f.symm.blockEquiv = f.blockEquiv.symm := by
  simp only [blockEquiv, toSimpleGraphIso_symm, SimpleGraph.Iso.blockEquiv_symm]

/-- Transport by an inverse multigraph isomorphism is inverse cut-vertex transport. -/
@[simp]
theorem cutVertexEquiv_symm (f : Iso G H) :
    f.symm.cutVertexEquiv = f.cutVertexEquiv.symm := by
  simp only [cutVertexEquiv, toSimpleGraphIso_symm, SimpleGraph.Iso.cutVertexEquiv_symm]

/-- The multigraph block--cut graph construction preserves identity isomorphisms. -/
@[simp]
theorem blockCutGraphIso_refl : (refl G).blockCutGraphIso = SimpleGraph.Iso.refl := by
  rw [blockCutGraphIso, toSimpleGraphIso_refl,
    SimpleGraph.Iso.blockCutGraphIso_refl]

/-- The multigraph block--cut graph construction preserves composition. -/
@[simp]
theorem blockCutGraphIso_trans (f : Iso G H) (g : Iso H K) :
    (f.trans g).blockCutGraphIso =
      g.blockCutGraphIso.comp f.blockCutGraphIso := by
  simp only [blockCutGraphIso, toSimpleGraphIso_trans,
    SimpleGraph.Iso.blockCutGraphIso_comp]

/-- The multigraph block--cut graph construction preserves inverse isomorphisms. -/
@[simp]
theorem blockCutGraphIso_symm (f : Iso G H) :
    f.symm.blockCutGraphIso = f.blockCutGraphIso.symm := by
  simp only [blockCutGraphIso, toSimpleGraphIso_symm,
    SimpleGraph.Iso.blockCutGraphIso_symm]

end Iso

end Graph
