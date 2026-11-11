/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Relabelling finite two-complexes

A bijection of vertices transports the edges and triangles of a `TwoComplex`, including
isolated vertices. Relabelling respects identities and composition and preserves the complete
complex. The induced equivalences of edge and triangle types, and the corresponding sum
formulas, allow edge costs and triangle defects to be reindexed without choosing orientations.
-/

public section

namespace TauCeti.TwoComplex

variable {V W U : Type*}

/-- Transport a two-complex along a bijection of its ambient vertex types. -/
def relabel (X : TwoComplex V) (e : V ≃ W) : TwoComplex W where
  edges := X.edges.map e.finsetCongr.toEmbedding
  triangles := X.triangles.map e.finsetCongr.toEmbedding
  edge_card := by
    intro s hs
    obtain ⟨s, hmem, rfl⟩ := Finset.mem_map.mp hs
    simpa using X.edge_card s hmem
  triangle_card := by
    intro s hs
    obtain ⟨s, hmem, rfl⟩ := Finset.mem_map.mp hs
    simpa using X.triangle_card s hmem
  edge_mem_of_subset := by
    intro t ht s hst hs
    rw [Finset.mem_map_equiv] at ht ⊢
    apply X.edge_mem_of_subset _ ht
    · exact Finset.map_subset_map.mpr hst
    · simpa [Equiv.finsetCongr_symm] using hs

theorem edges_relabel (X : TwoComplex V) (e : V ≃ W) :
    (X.relabel e).edges = X.edges.map e.finsetCongr.toEmbedding := (rfl)

theorem triangles_relabel (X : TwoComplex V) (e : V ≃ W) :
    (X.relabel e).triangles = X.triangles.map e.finsetCongr.toEmbedding := (rfl)

@[simp]
theorem mem_edges_relabel (X : TwoComplex V) (e : V ≃ W) (s : Finset W) :
    s ∈ (X.relabel e).edges ↔ s.map e.symm.toEmbedding ∈ X.edges := by
  simp [edges_relabel, Equiv.finsetCongr_symm]

@[simp]
theorem mem_triangles_relabel (X : TwoComplex V) (e : V ≃ W) (s : Finset W) :
    s ∈ (X.relabel e).triangles ↔ s.map e.symm.toEmbedding ∈ X.triangles := by
  simp [triangles_relabel, Equiv.finsetCongr_symm]

@[simp 1100]
theorem map_mem_edges_relabel (X : TwoComplex V) (e : V ≃ W) (s : Finset V) :
    s.map e.toEmbedding ∈ (X.relabel e).edges ↔ s ∈ X.edges := by
  exact Finset.mem_map' e.finsetCongr.toEmbedding

@[simp 1100]
theorem map_mem_triangles_relabel (X : TwoComplex V) (e : V ≃ W) (s : Finset V) :
    s.map e.toEmbedding ∈ (X.relabel e).triangles ↔ s ∈ X.triangles := by
  exact Finset.mem_map' e.finsetCongr.toEmbedding

@[simp]
theorem relabel_refl (X : TwoComplex V) : X.relabel (Equiv.refl V) = X := by
  ext <;> simp [edges_relabel, triangles_relabel]

/-- Successive relabellings agree with relabelling by the composite bijection. -/
@[simp]
theorem relabel_relabel (X : TwoComplex V) (e : V ≃ W) (f : W ≃ U) :
    (X.relabel e).relabel f = X.relabel (e.trans f) := by
  ext <;> simp [edges_relabel, triangles_relabel, Finset.map_map,
    ← Equiv.finsetCongr_trans]

/-- Relabelling is an equivalence of types of two-complexes. -/
def relabelEquiv (e : V ≃ W) : TwoComplex V ≃ TwoComplex W where
  toFun X := X.relabel e
  invFun X := X.relabel e.symm
  left_inv X := by simp
  right_inv X := by simp

@[simp]
theorem relabelEquiv_apply (e : V ≃ W) (X : TwoComplex V) :
    relabelEquiv e X = X.relabel e := (rfl)

@[simp]
theorem relabelEquiv_symm (e : V ≃ W) : (relabelEquiv e).symm = relabelEquiv e.symm := (rfl)

/-- A relabelling gives a bijection between the unoriented edges. -/
def edgeEquiv (X : TwoComplex V) (e : V ≃ W) : X.edges ≃ (X.relabel e).edges :=
  e.finsetCongr.subtypeEquiv fun s => by simp

@[simp]
theorem edgeEquiv_apply (X : TwoComplex V) (e : V ≃ W) (s : X.edges) :
    (X.edgeEquiv e s : Finset W) = (s : Finset V).map e.toEmbedding := (rfl)

@[simp]
theorem edgeEquiv_symm_apply (X : TwoComplex V) (e : V ≃ W)
    (s : (X.relabel e).edges) :
    ((X.edgeEquiv e).symm s : Finset V) = (s : Finset W).map e.symm.toEmbedding := (rfl)

/-- A relabelling gives a bijection between the unoriented triangles. -/
def triangleEquiv (X : TwoComplex V) (e : V ≃ W) :
    X.triangles ≃ (X.relabel e).triangles :=
  e.finsetCongr.subtypeEquiv fun s => by simp

@[simp]
theorem triangleEquiv_apply (X : TwoComplex V) (e : V ≃ W) (s : X.triangles) :
    (X.triangleEquiv e s : Finset W) = (s : Finset V).map e.toEmbedding := (rfl)

@[simp]
theorem triangleEquiv_symm_apply (X : TwoComplex V) (e : V ≃ W)
    (s : (X.relabel e).triangles) :
    ((X.triangleEquiv e).symm s : Finset V) = (s : Finset W).map e.symm.toEmbedding := (rfl)

@[simp]
theorem card_edges_relabel (X : TwoComplex V) (e : V ≃ W) :
    (X.relabel e).edges.card = X.edges.card := by simp [edges_relabel]

@[simp]
theorem card_triangles_relabel (X : TwoComplex V) (e : V ≃ W) :
    (X.relabel e).triangles.card = X.triangles.card := by simp [triangles_relabel]

/-- Reindex an unoriented edge sum along a vertex bijection. -/
theorem sum_edges_relabel {A : Type*} [AddCommMonoid A]
    (X : TwoComplex V) (e : V ≃ W) (f : Finset W → A) :
    ∑ s ∈ (X.relabel e).edges, f s = ∑ s ∈ X.edges, f (s.map e.toEmbedding) := by
  simp [edges_relabel]

/-- Reindex an unoriented triangle sum along a vertex bijection. -/
theorem sum_triangles_relabel {A : Type*} [AddCommMonoid A]
    (X : TwoComplex V) (e : V ≃ W) (f : Finset W → A) :
    ∑ s ∈ (X.relabel e).triangles, f s = ∑ s ∈ X.triangles, f (s.map e.toEmbedding) := by
  simp [triangles_relabel]

/-- A bijection carries the complete complex to the complete complex, also for empty or
singleton vertex types. -/
@[simp]
theorem relabel_complete [Fintype V] [Fintype W] (e : V ≃ W) :
    (complete V).relabel e = complete W := by
  ext s <;> simp

end TauCeti.TwoComplex
