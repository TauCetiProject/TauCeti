/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Defs

/-!
# Cochains are determined on edges, up to normalization

A `Cochain X G` of `Defs` stores a value on every ordered pair of vertices, but its axiom and
every quantity built from it (`defect`, `cost`, `gaugeDist`, hence `h1`) only read the values on
edges. This file makes that precise without changing the structure:

* `Cochain.canonicalize` resets every value off the edges to `1`;
* `Cochain.ext_edges`: two cochains that are `1` off the edges and agree on the edges are equal;
* `Cochain.canonicalize_ext`: cochains agreeing on the edges have the same canonical form;
* `Cochain.defect_eq_of_edges`, `Cochain.cost_eq_of_edges`, `Cochain.gaugeDist_eq_of_edges`:
  the defect, the costs and the gauge distance only depend on the values on edges.
-/

public section

open Finset

namespace TauCeti.CoboundaryExpansion

namespace Cochain

variable {V : Type*} [LinearOrder V] {G : Type*} [Group G] {X : TwoComplex V}

/-- The cochain with the same values on the edges and the value `1` off the edges. -/
def canonicalize (α : Cochain X G) : Cochain X G where
  toFun u v := if ({u, v} : Finset V) ∈ X.edges then α.toFun u v else 1
  inv_symm u v h := by
    have hvu : ({v, u} : Finset V) ∈ X.edges := by rwa [pair_comm]
    rw [ite_eq_left hvu, ite_eq_left h, α.inv_symm u v h]

/-- The canonical form keeps the values on edges. -/
theorem canonicalize_toFun_of_mem (α : Cochain X G) {u v : V}
    (h : ({u, v} : Finset V) ∈ X.edges) : α.canonicalize.toFun u v = α.toFun u v :=
  ite_eq_left h

/-- The canonical form is `1` off the edges. -/
theorem canonicalize_toFun_of_not_mem (α : Cochain X G) {u v : V}
    (h : ({u, v} : Finset V) ∉ X.edges) : α.canonicalize.toFun u v = 1 :=
  ite_eq_right h

/-- Two cochains that are `1` off the edges and agree on the edges are equal. -/
theorem ext_edges {α β : Cochain X G}
    (hα : ∀ u v, ({u, v} : Finset V) ∉ X.edges → α.toFun u v = 1)
    (hβ : ∀ u v, ({u, v} : Finset V) ∉ X.edges → β.toFun u v = 1)
    (h : ∀ u v, ({u, v} : Finset V) ∈ X.edges → α.toFun u v = β.toFun u v) : α = β := by
  obtain ⟨f, hf⟩ := α
  obtain ⟨g, hg⟩ := β
  congr
  funext u v
  by_cases he : ({u, v} : Finset V) ∈ X.edges
  · exact h u v he
  · exact (hα u v he).trans (hβ u v he).symm

/-- Cochains that agree on the edges have the same canonical form. -/
theorem canonicalize_ext {α β : Cochain X G}
    (h : ∀ u v, ({u, v} : Finset V) ∈ X.edges → α.toFun u v = β.toFun u v) :
    α.canonicalize = β.canonicalize :=
  ext_edges (fun _ _ he => canonicalize_toFun_of_not_mem α he)
    (fun _ _ he => canonicalize_toFun_of_not_mem β he)
    (fun u v he => by
      rw [canonicalize_toFun_of_mem α he, canonicalize_toFun_of_mem β he, h u v he])

/-- The defect only depends on the values on edges. -/
theorem defect_eq_of_edges [Fintype V] (ℓ : GroupNorm G) {α β : Cochain X G}
    (h : ∀ u v, ({u, v} : Finset V) ∈ X.edges → α.toFun u v = β.toFun u v) :
    α.defect ℓ = β.defect ℓ := by
  unfold defect
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨-, h12, h23, hT⟩ := mem_filter.1 hp
  -- The three sides of a triangle are edges.
  have side : ∀ a b : V, a ≠ b → a ∈ ({p.1, p.2.1, p.2.2} : Finset V) →
      b ∈ ({p.1, p.2.1, p.2.2} : Finset V) → ({a, b} : Finset V) ∈ X.edges :=
    fun a b hab ha hb => X.edge_mem_of_subset _ hT _ (insert_subset ha (singleton_subset_iff.2 hb))
      (card_pair hab)
  rw [h _ _ (side _ _ h12.ne (by simp) (by simp)), h _ _ (side _ _ h23.ne (by simp) (by simp)),
    h _ _ (side _ _ (h12.trans h23).ne' (by simp) (by simp))]

/-- The cost of a gauge only depends on the values on edges. -/
theorem cost_eq_of_edges [Fintype V] (ℓ : GroupNorm G) {α β : Cochain X G}
    (h : ∀ u v, ({u, v} : Finset V) ∈ X.edges → α.toFun u v = β.toFun u v) (γ : V → G) :
    α.cost ℓ γ = β.cost ℓ γ := by
  unfold cost
  refine sum_congr rfl fun p hp => ?_
  rw [h _ _ (mem_filter.1 hp).2.2]

/-- The gauge distance only depends on the values on edges. -/
theorem gaugeDist_eq_of_edges [Fintype V] (ℓ : GroupNorm G) {α β : Cochain X G}
    (h : ∀ u v, ({u, v} : Finset V) ∈ X.edges → α.toFun u v = β.toFun u v) :
    α.gaugeDist ℓ = β.gaugeDist ℓ := by
  unfold gaugeDist
  simp only [cost_eq_of_edges ℓ h]

/-- Canonicalizing does not change the defect. -/
theorem defect_canonicalize [Fintype V] (ℓ : GroupNorm G) (α : Cochain X G) :
    α.canonicalize.defect ℓ = α.defect ℓ :=
  defect_eq_of_edges ℓ fun _ _ he => canonicalize_toFun_of_mem α he

/-- Canonicalizing does not change the gauge distance. -/
theorem gaugeDist_canonicalize [Fintype V] (ℓ : GroupNorm G) (α : Cochain X G) :
    α.canonicalize.gaugeDist ℓ = α.gaugeDist ℓ :=
  gaugeDist_eq_of_edges ℓ fun _ _ he => canonicalize_toFun_of_mem α he

end Cochain

end TauCeti.CoboundaryExpansion
