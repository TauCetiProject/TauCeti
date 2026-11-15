/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Vertex links and weighted triangle incidence

The edges in the link of a vertex `x` are the edges opposite `x` in filled triangles.
Inserting `x` identifies these link edges with the triangles containing `x`. Consequently,
summing a triangle weight over all vertex links counts each triangle exactly three times.
No vertex order or orientation is needed, and the weights may lie in any additive
commutative monoid.

This double count is the combinatorial part of the star-gauge identity: an edge opposite
the star vertex contributes the weight of its triangle, while incident edges contribute zero.
See Chapman–Lubotzky, *Stability of homomorphisms, coverings and cocycles II*,
Proposition 3.2, and Beasley, *The Permutation Coboundary Constant of the Complete Complex
Is k/3 for Every k≥4*, Proposition 1.
-/

public section

open Finset

namespace TauCeti.TwoComplex

variable {V A : Type*} [DecidableEq V]

/-- The edges opposite `x` in the filled triangles containing `x`. -/
def linkEdges (X : TwoComplex V) (x : V) : Finset (Finset V) :=
  X.edges.filter fun e => x ∉ e ∧ insert x e ∈ X.triangles

/-- Membership in a vertex link is determined by the opposite edge and its triangle. -/
@[simp]
theorem mem_linkEdges (X : TwoComplex V) (x : V) (e : Finset V) :
    e ∈ X.linkEdges x ↔ e ∈ X.edges ∧ x ∉ e ∧ insert x e ∈ X.triangles := by
  simp [linkEdges]

/-- Removing a vertex from a triangle gives an edge in its link. -/
theorem erase_mem_linkEdges (X : TwoComplex V) {t : Finset V} (ht : t ∈ X.triangles)
    {x : V} (hx : x ∈ t) : t.erase x ∈ X.linkEdges x := by
  have hc : (t.erase x).card = 2 := by
    rw [card_erase_of_mem hx, X.triangle_card t ht]
  exact (X.mem_linkEdges x _).2
    ⟨X.edge_mem_of_subset t ht _ (erase_subset _ _) hc,
      notMem_erase _ _, by simpa [insert_erase hx] using ht⟩

/-- Inserting the link vertex reindexes link edges as triangles through that vertex. -/
theorem sum_linkEdges [AddCommMonoid A] (X : TwoComplex V) (x : V)
    (f : Finset V → A) :
    ∑ e ∈ X.linkEdges x, f (insert x e) =
      ∑ t ∈ X.triangles.filter (x ∈ ·), f t := by
  apply sum_bij (fun e _ => insert x e)
  · intro e he
    exact mem_filter.mpr ⟨(X.mem_linkEdges x e).mp he |>.2.2, mem_insert_self _ _⟩
  · intro e he e' he' h
    have hx := (X.mem_linkEdges x e).mp he |>.2.1
    have hx' := (X.mem_linkEdges x e').mp he' |>.2.1
    simpa [hx, hx'] using congrArg (fun t => t.erase x) h
  · intro t ht
    obtain ⟨ht, hx⟩ := mem_filter.mp ht
    exact ⟨t.erase x, X.erase_mem_linkEdges ht hx, insert_erase hx⟩
  · intro e _
    rfl

/-- Summing triangle weights over all vertex links counts each triangle three times.
This also holds for complexes with no triangles and for the empty vertex type. -/
theorem sum_vertex_linkEdges [Fintype V] [AddCommMonoid A] (X : TwoComplex V)
    (f : Finset V → A) :
    ∑ x : V, ∑ e ∈ X.linkEdges x, f (insert x e) =
      3 • ∑ t ∈ X.triangles, f t := by
  simp_rw [sum_linkEdges, sum_filter]
  rw [sum_comm, smul_sum]
  apply sum_congr rfl
  intro t ht
  simp [X.triangle_card t ht]

/-- The total number of edges in all vertex links is three times the triangle count. -/
theorem sum_card_linkEdges [Fintype V] (X : TwoComplex V) :
    ∑ x : V, (X.linkEdges x).card = 3 * X.triangles.card := by
  simpa [nsmul_eq_mul] using X.sum_vertex_linkEdges (fun _ => (1 : ℕ))

/-- The link of a vertex in the complete complex consists of every pair avoiding that vertex. -/
@[simp]
theorem linkEdges_complete [Fintype V] (x : V) :
    (complete V).linkEdges x = (univ.erase x).powersetCard 2 := by
  ext e
  simp only [mem_linkEdges, mem_edges_complete, mem_triangles_complete, mem_powersetCard]
  constructor
  · rintro ⟨he, hx, _⟩
    exact ⟨by simpa [subset_iff] using hx, he⟩
  · rintro ⟨he, hc⟩
    have hx : x ∉ e := by
      intro hx
      exact (mem_erase.mp (he hx)).1 rfl
    exact ⟨hc, hx, by simp [card_insert_of_notMem hx, hc]⟩

/-- The weighted star double count on the complete complex. Edges containing the star vertex
contribute zero; every other edge contributes the weight of the triangle it spans with it. -/
theorem sum_vertex_edges_complete [Fintype V] [AddCommMonoid A] (f : Finset V → A) :
    ∑ x : V, ∑ e ∈ (complete V).edges, (if x ∈ e then 0 else f (insert x e)) =
      3 • ∑ t ∈ (complete V).triangles, f t := by
  rw [← sum_vertex_linkEdges (complete V) f]
  apply sum_congr rfl
  intro x _
  rw [linkEdges, sum_filter]
  apply sum_congr rfl
  intro e he
  have hc := (mem_edges_complete e).mp he
  by_cases hx : x ∈ e
  · simp [hx]
  · simp [hx, card_insert_of_notMem hx, hc]

end TauCeti.TwoComplex
