/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Symmetric differences of simple graphs and cut switching

Two simple graphs `G₁` and `G₂` on the same vertex type have symmetric difference `G₁ ∆ G₂` in the
Boolean algebra `SimpleGraph V`: two vertices are adjacent in `G₁ ∆ G₂` precisely when they are
adjacent in one of `G₁`, `G₂` and not the other (`Xor`). Passing to edge sets or edge finsets
carries graph symmetric difference to set or finset symmetric difference.

For a vertex set `S : Set V`, the complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ` joins `u`
and `v` precisely when `Xor (u ∈ S) (v ∈ S)` (which already forces `u ≠ v`). Around any triple of
vertices `(u, v, w)`, the three cut conditions cancel in pairs, so switching a graph `G` by
`(⊤ : SimpleGraph V).between S Sᶜ` preserves the triangle edge-parity
`Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u))` on every triple and hence the count of ordered
triples spanning an odd number of edges.

## Main results

* `SimpleGraph.SymmDiff.adjDecidable`: decidable adjacency instance for `G₁ ∆ G₂`.
* `SimpleGraph.symmDiff_adj`, `SimpleGraph.edgeSet_symmDiff`, `SimpleGraph.edgeFinset_symmDiff`:
  adjacency, edge set, and edge finset of `G₁ ∆ G₂`.
* `SimpleGraph.top_between_compl_adj`: adjacency in `(⊤ : SimpleGraph V).between S Sᶜ` is
  `Xor (u ∈ S) (v ∈ S)`.
* `SimpleGraph.symmDiff_top_between_symmDiff`: switching twice by cuts `S` and `T` is switching
  once by `S ∆ T`.
* `SimpleGraph.xor_symmDiff_top_between_compl_adj` and
  `SimpleGraph.card_filter_lt_triple_xor_symmDiff_top_between`: cut switching preserves triangle
  edge-parity pointwise and in total across strictly increasing vertex triples.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

/-- Adjacency in a symmetric difference of graphs with decidable adjacency is decidable. -/
instance SymmDiff.adjDecidable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G ∆ H).Adj :=
  inferInstanceAs <| DecidableRel fun u v ↦ Xor (G.Adj u v) (H.Adj u v)

/-- Two vertices are adjacent in `G₁ ∆ G₂` precisely when they are adjacent in exactly one of `G₁`
and `G₂`. -/
@[simp, grind =]
theorem symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v : V) :
    (G₁ ∆ G₂).Adj u v ↔ Xor (G₁.Adj u v) (G₂.Adj u v) :=
  (Iff.rfl)

/-- The edge set of `G₁ ∆ G₂` is the symmetric difference of the edge sets of `G₁` and `G₂`. -/
@[simp]
theorem edgeSet_symmDiff (G₁ G₂ : SimpleGraph V) :
    (G₁ ∆ G₂).edgeSet = G₁.edgeSet ∆ G₂.edgeSet := by
  rw [symmDiff_def, edgeSet_sup, edgeSet_sdiff, edgeSet_sdiff, symmDiff_def]

/-- The edge finset of `G₁ ∆ G₂` is the symmetric difference of the edge finsets of `G₁` and
`G₂`. -/
@[simp]
theorem edgeFinset_symmDiff (G₁ G₂ : SimpleGraph V) [DecidableEq V]
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] [Fintype (G₁ ∆ G₂).edgeSet] :
    (G₁ ∆ G₂).edgeFinset = G₁.edgeFinset ∆ G₂.edgeFinset :=
  coe_injective <| by rw [coe_symmDiff, coe_edgeFinset, coe_edgeFinset, coe_edgeFinset,
    edgeSet_symmDiff]

/-- Adjacency in `G.between S Sᶜ` holds precisely when the endpoints are adjacent in `G` and lie on
opposite sides of `S`. -/
theorem between_compl_adj (G : SimpleGraph V) (S : Set V) (u v : V) :
    (G.between S Sᶜ).Adj u v ↔ G.Adj u v ∧ Xor (u ∈ S) (v ∈ S) := by
  rw [between_adj, Set.mem_compl_iff, Set.mem_compl_iff]
  grind

/-- Adjacency in the complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ` is `Xor (u ∈ S) (v ∈ S)`:
the distinctness condition `u ≠ v` is automatic when `u` and `v` lie on opposite sides of `S`. -/
@[simp, grind =]
theorem top_between_compl_adj (S : Set V) (u v : V) :
    ((⊤ : SimpleGraph V).between S Sᶜ).Adj u v ↔ Xor (u ∈ S) (v ∈ S) := by
  rw [between_compl_adj, top_adj]
  exact ⟨And.right, fun h ↦ ⟨fun huv ↦ by subst huv; exact (xor_self (u ∈ S)).mp h, h⟩⟩

/-- Removing the edges of `G` from the complete-graph cut across `S` gives the cut of `Gᶜ` across
`S`. -/
theorem top_between_sdiff_eq_compl_between (G : SimpleGraph V) (S : Set V) :
    (⊤ : SimpleGraph V).between S Sᶜ \ G = Gᶜ.between S Sᶜ := by
  ext u v
  rw [sdiff_adj, top_between_compl_adj, between_compl_adj, compl_adj]
  exact ⟨fun ⟨hxor, hnadj⟩ ↦ ⟨⟨fun huv ↦ by subst huv; exact (xor_self _).mp hxor, hnadj⟩, hxor⟩,
    fun ⟨⟨_, hnadj⟩, hxor⟩ ↦ ⟨hxor, hnadj⟩⟩

/-- The edges of `G` across the singleton cut `({v}, {v}ᶜ)` are precisely the edges incident to
`v`. -/
@[simp]
theorem edgeSet_between_singleton_compl (G : SimpleGraph V) (v : V) :
    (G.between {v} ({v} : Set V)ᶜ).edgeSet = G.incidenceSet v := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_edgeSet, between_adj, Set.mem_singleton_iff, Set.mem_compl_iff,
      mk'_mem_incidenceSet_iff]
    exact ⟨fun ⟨h, h'⟩ ↦ ⟨h, by rcases h' with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp⟩,
      fun ⟨h, h'⟩ ↦ ⟨h, by
        rcases h' with rfl | rfl
        exacts [Or.inl ⟨rfl, h.ne'⟩, Or.inr ⟨h.ne, rfl⟩]⟩⟩

/-- Switching `G` successively by the complete-graph cuts of `S` and `T` is switching once by the
complete-graph cut of `S ∆ T`. -/
theorem symmDiff_top_between_symmDiff (G : SimpleGraph V) (S T : Set V) :
    G ∆ (⊤ : SimpleGraph V).between S Sᶜ ∆ (⊤ : SimpleGraph V).between T Tᶜ =
      G ∆ (⊤ : SimpleGraph V).between (S ∆ T) (S ∆ T)ᶜ := by
  rw [symmDiff_assoc, ← top_between_symmDiff]

/-- Around any three vertices, triangle edge-parity in `G₁ ∆ G₂` is the `Xor` of the triangle
edge-parities in `G₁` and `G₂`. -/
theorem xor_symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v w : V) :
    Xor ((G₁ ∆ G₂).Adj u v) (Xor ((G₁ ∆ G₂).Adj v w) ((G₁ ∆ G₂).Adj w u)) ↔
      Xor (Xor (G₁.Adj u v) (Xor (G₁.Adj v w) (G₁.Adj w u)))
        (Xor (G₂.Adj u v) (Xor (G₂.Adj v w) (G₂.Adj w u))) := by
  simp only [symmDiff_adj]
  grind

/-- A complete-graph cut meets every vertex triple in an even number of edges. -/
theorem not_xor_top_between_compl_adj (S : Set V) (u v w : V) :
    ¬ Xor (((⊤ : SimpleGraph V).between S Sᶜ).Adj u v)
      (Xor (((⊤ : SimpleGraph V).between S Sᶜ).Adj v w)
        (((⊤ : SimpleGraph V).between S Sᶜ).Adj w u)) := by
  simp only [top_between_compl_adj]
  grind

/-- Switching a graph by a complete-graph cut preserves triangle edge-parity on every vertex
triple. -/
theorem xor_symmDiff_top_between_compl_adj (G : SimpleGraph V) (S : Set V) (u v w : V) :
    Xor ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj u v)
      (Xor ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj v w)
        ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj w u)) ↔
      Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u)) := by
  simp only [symmDiff_adj, top_between_compl_adj]
  grind

/-- Switching a finite ordered graph by a complete-graph cut preserves the number of strictly
increasing vertex triples spanning an odd number of edges. -/
theorem card_filter_lt_triple_xor_symmDiff_top_between [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] :
    #{p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
      Xor ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj p.1 p.2.1)
        (Xor ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj p.2.1 p.2.2)
          ((G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj p.2.2 p.1))} =
    #{p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
      Xor (G.Adj p.1 p.2.1) (Xor (G.Adj p.2.1 p.2.2) (G.Adj p.2.2 p.1))} := by
  congr 1
  ext ⟨u, v, w⟩
  simp only [mem_filter, mem_univ, true_and, xor_symmDiff_top_between_compl_adj]

end SimpleGraph
