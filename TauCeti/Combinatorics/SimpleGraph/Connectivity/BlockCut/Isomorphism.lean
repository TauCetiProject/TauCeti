/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.BlockCut.Basic

/-!
# Isomorphisms of block--cut graphs

A graph isomorphism sends blocks to their vertex-set images and cut vertices to their images.
These two equivalences preserve incidence and thus give an isomorphism of block--cut graphs.
The construction respects identity, inverse and composition, so the incidence graph and its
walks can be transported without making any choices of blocks or cut vertices. No finiteness
hypothesis is needed.
-/

public section

namespace SimpleGraph.Iso

variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}

/-- The equivalence of blocks induced by a graph isomorphism. -/
def blockEquiv (e : G ≃g H) : G.BlockVertex ≃ H.BlockVertex :=
  e.toEquiv.setCongr.subtypeEquiv fun _ ↦ e.isBlock_image_iff.symm

/-- Transporting a block takes the image of its vertex set. -/
@[simp]
theorem coe_blockEquiv_apply (e : G ≃g H) (B : G.BlockVertex) :
    (e.blockEquiv B : Set W) = e '' (B : Set V) :=
  (rfl)

/-- Inverse transport of a block takes its inverse image under the vertex equivalence. -/
@[simp]
theorem coe_blockEquiv_symm_apply (e : G ≃g H) (B : H.BlockVertex) :
    (e.blockEquiv.symm B : Set V) = e.symm '' (B : Set W) :=
  (rfl)

/-- The equivalence of cut vertices induced by a graph isomorphism. -/
def cutVertexEquiv (e : G ≃g H) : G.CutVertex ≃ H.CutVertex :=
  e.toEquiv.subtypeEquiv fun _ ↦ e.isCutVertex_iff.symm

/-- Transport of a cut vertex agrees with the original vertex map. -/
@[simp]
theorem coe_cutVertexEquiv_apply (e : G ≃g H) (v : G.CutVertex) :
    (e.cutVertexEquiv v : W) = e v :=
  (rfl)

/-- Inverse transport of a cut vertex agrees with the inverse vertex map. -/
@[simp]
theorem coe_cutVertexEquiv_symm_apply (e : G ≃g H) (v : H.CutVertex) :
    (e.cutVertexEquiv.symm v : V) = e.symm v :=
  (rfl)

/-- Graph isomorphisms induce isomorphisms of their block--cut incidence graphs. -/
def blockCutGraphIso (e : G ≃g H) : G.blockCutGraph ≃g H.blockCutGraph where
  toEquiv := Equiv.sumCongr e.blockEquiv e.cutVertexEquiv
  map_rel_iff' := by
    rintro (B | v) (C | w) <;> simp [Set.mem_image, e.injective.eq_iff]

/-- A block vertex is sent to the corresponding block vertex. -/
@[simp]
theorem blockCutGraphIso_apply_block (e : G ≃g H) (B : G.BlockVertex) :
    e.blockCutGraphIso (.inl B) = .inl (e.blockEquiv B) :=
  (rfl)

/-- A cut vertex is sent to the corresponding cut vertex. -/
@[simp]
theorem blockCutGraphIso_apply_cutVertex (e : G ≃g H) (v : G.CutVertex) :
    e.blockCutGraphIso (.inr v) = .inr (e.cutVertexEquiv v) :=
  (rfl)

/-- The inverse incidence-graph map sends a block vertex back to its original block. -/
@[simp]
theorem blockCutGraphIso_symm_apply_block (e : G ≃g H) (B : H.BlockVertex) :
    e.blockCutGraphIso.symm (.inl B) = .inl (e.blockEquiv.symm B) :=
  (rfl)

/-- The inverse incidence-graph map sends a cut vertex back to its original vertex. -/
@[simp]
theorem blockCutGraphIso_symm_apply_cutVertex (e : G ≃g H) (v : H.CutVertex) :
    e.blockCutGraphIso.symm (.inr v) = .inr (e.cutVertexEquiv.symm v) :=
  (rfl)

/-- Identity graph isomorphisms act identically on blocks. -/
@[simp]
theorem blockEquiv_refl : (Iso.refl : G ≃g G).blockEquiv = Equiv.refl _ := by
  ext B x
  simp

/-- Identity graph isomorphisms act identically on cut vertices. -/
@[simp]
theorem cutVertexEquiv_refl : (Iso.refl : G ≃g G).cutVertexEquiv = Equiv.refl _ := by
  ext v
  rfl

/-- Block transport commutes with composition. -/
@[simp]
theorem blockEquiv_comp (e : G ≃g H) (f : H ≃g K) :
    (f.comp e).blockEquiv = e.blockEquiv.trans f.blockEquiv := by
  ext B x
  simp [Set.mem_image]

/-- Cut-vertex transport commutes with composition. -/
@[simp]
theorem cutVertexEquiv_comp (e : G ≃g H) (f : H ≃g K) :
    (f.comp e).cutVertexEquiv = e.cutVertexEquiv.trans f.cutVertexEquiv := by
  ext v
  rfl

/-- Transport by an inverse graph isomorphism is inverse block transport. -/
@[simp]
theorem blockEquiv_symm (e : G ≃g H) : e.symm.blockEquiv = e.blockEquiv.symm := by
  ext B x
  rfl

/-- Transport by an inverse graph isomorphism is inverse cut-vertex transport. -/
@[simp]
theorem cutVertexEquiv_symm (e : G ≃g H) : e.symm.cutVertexEquiv = e.cutVertexEquiv.symm := by
  ext v
  rfl

/-- The block--cut graph construction preserves identity isomorphisms. -/
@[simp]
theorem blockCutGraphIso_refl :
    (Iso.refl : G ≃g G).blockCutGraphIso = Iso.refl := by
  ext (B | v) <;> simp

/-- The block--cut graph construction preserves composition. -/
@[simp]
theorem blockCutGraphIso_comp (e : G ≃g H) (f : H ≃g K) :
    (f.comp e).blockCutGraphIso = f.blockCutGraphIso.comp e.blockCutGraphIso := by
  ext (B | v) <;> simp

/-- The block--cut graph construction preserves inverse isomorphisms. -/
@[simp]
theorem blockCutGraphIso_symm (e : G ≃g H) :
    e.symm.blockCutGraphIso = e.blockCutGraphIso.symm := by
  ext (B | v) <;> simp

end SimpleGraph.Iso
