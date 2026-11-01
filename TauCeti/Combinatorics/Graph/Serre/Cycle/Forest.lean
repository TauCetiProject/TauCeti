/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Spanning forests of chosen Serre darts

A set of darts is regarded as a multigraph with those actual edges. Its simple support
retains every vertex and records connectivity, while forgetting loops and parallel edges.
A spanning forest chooses actual darts, contains no loops or parallel edges, and has the
same connectivity as the original set. Such forests exist, even for infinite graphs.

For finitely many vertices, the number of forest darts plus the number of components is
the number of vertices. No connectedness or nonemptiness assumption is needed. The chosen
darts, rather than their endpoint pairs, provide the forest coordinates used in cycle bases.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.3.
* R. Diestel, *Graph Theory*, §1.9 (spanning forests and fundamental cycle bases).
-/

public section

namespace TauCeti.SerreGraph

universe u v

variable (Γ : SerreGraph.{u, v}) (O : Set Γ.E)

/-- The simple graph recording connectivity of the actual darts in `O`. All vertices remain,
including isolated vertices; loops disappear and parallel darts give the same adjacency. -/
def supportGraph : SimpleGraph Γ.V :=
  SimpleGraph.fromRel fun x y => ∃ e ∈ O, Γ.src e = x ∧ Γ.tgt e = y

/-- Adjacency means that a non-loop dart joins the two vertices in either direction. -/
@[simp] theorem supportGraph_adj (x y : Γ.V) :
    (Γ.supportGraph O).Adj x y ↔ x ≠ y ∧
      ((∃ e ∈ O, Γ.src e = x ∧ Γ.tgt e = y) ∨
        ∃ e ∈ O, Γ.src e = y ∧ Γ.tgt e = x) :=
  SimpleGraph.fromRel_adj _ x y

/-- The simple support edges are exactly the endpoint pairs of non-loop chosen darts. -/
theorem supportGraph_edgeSet :
    (Γ.supportGraph O).edgeSet =
      (fun e => s(Γ.src e, Γ.tgt e)) '' {e | e ∈ O ∧ Γ.src e ≠ Γ.tgt e} := by
  ext q
  induction q using Sym2.ind with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeSet, supportGraph_adj, Set.mem_image, Set.mem_ofPred_eq,
      Sym2.eq_iff]
    aesop

/-- For a loopless dart set, every dart contributes an edge to the simple support. -/
theorem supportGraph_edgeSet_of_src_ne_tgt (h : ∀ e ∈ O, Γ.src e ≠ Γ.tgt e) :
    (Γ.supportGraph O).edgeSet = (fun e => s(Γ.src e, Γ.tgt e)) '' O := by
  rw [supportGraph_edgeSet, Set.sep_eq_self_iff_mem_true.mpr h]

/-- Enlarging the dart set enlarges its simple support. -/
theorem supportGraph_mono {O O' : Set Γ.E} (h : O ⊆ O') :
    Γ.supportGraph O ≤ Γ.supportGraph O' := by
  intro x y hxy
  rw [supportGraph_adj] at hxy ⊢
  aesop

@[simp] theorem supportGraph_empty : Γ.supportGraph ∅ = ⊥ := by
  ext x y
  simp [supportGraph_adj]

/-- A spanning forest on actual chosen darts. Besides acyclicity of the simple support,
loops and repeated unordered endpoint pairs are excluded explicitly. -/
structure IsSpanningForest (F : Set Γ.E) : Prop where
  /-- Every forest dart was present in the chosen ambient multigraph. -/
  subset : F ⊆ O
  /-- A forest has no loops. -/
  src_ne_tgt : ∀ e ∈ F, Γ.src e ≠ Γ.tgt e
  /-- A forest has no parallel edges, in either direction. -/
  endpoints_injOn : Set.InjOn (fun e => s(Γ.src e, Γ.tgt e)) F
  /-- The simple support has no cycles. -/
  isAcyclic : (Γ.supportGraph F).IsAcyclic
  /-- The forest connects exactly the same pairs of vertices. -/
  reachable_eq : (Γ.supportGraph F).Reachable = (Γ.supportGraph O).Reachable

variable {Γ O} {F : Set Γ.E}

/-- Endpoint pairs identify forest darts bijectively with the edges of the simple support.
This identification retains the chosen actual edge above each endpoint pair. -/
theorem IsSpanningForest.bijOn_endpoints (hF : Γ.IsSpanningForest O F) :
    Set.BijOn (fun e => s(Γ.src e, Γ.tgt e)) F (Γ.supportGraph F).edgeSet := by
  rw [Γ.supportGraph_edgeSet_of_src_ne_tgt F hF.src_ne_tgt]
  exact ⟨Set.mapsTo_image _ _, hF.endpoints_injOn, Set.surjOn_image _ _⟩

/-- A spanning forest on finitely many vertices has finitely many actual darts, even if
the ambient multigraph has infinitely many loops or parallel edges. -/
theorem IsSpanningForest.finite [Finite Γ.V] (hF : Γ.IsSpanningForest O F) : F.Finite :=
  hF.bijOn_endpoints.finite_iff_finite.mpr (Set.toFinite _)

/-- Every chosen set of darts admits a spanning forest of actual edges. No finiteness,
orientation, connectedness or nonemptiness is required. -/
theorem exists_spanningForest (Γ : SerreGraph.{u, v}) (O : Set Γ.E) :
    ∃ F, Γ.IsSpanningForest O F := by
  obtain ⟨H, hHO, hH, hreach⟩ := (Γ.supportGraph O).exists_isAcyclic_reachable_eq_le
  have hsurj : Set.SurjOn (fun e => s(Γ.src e, Γ.tgt e))
      {e | e ∈ O ∧ Γ.src e ≠ Γ.tgt e} H.edgeSet := by
    intro q hq
    have hq' := SimpleGraph.edgeSet_mono hHO hq
    rwa [Γ.supportGraph_edgeSet O] at hq'
  obtain ⟨F, hFO, hbij⟩ := hsurj.exists_bijOn_subset
  have hsupport : Γ.supportGraph F = H := by
    apply SimpleGraph.edgeSet_injective
    rw [Γ.supportGraph_edgeSet_of_src_ne_tgt F (fun _ he => (hFO he).2), hbij.image_eq]
  exact ⟨F, ⟨fun _ he => (hFO he).1, fun _ he => (hFO he).2,
    hbij.injOn, hsupport ▸ hH, hsupport ▸ hreach⟩⟩

/-- On finitely many vertices, forest darts plus ambient components equal vertices.
This includes disconnected graphs and the empty graph. -/
theorem IsSpanningForest.card [Finite Γ.V] (hF : Γ.IsSpanningForest O F) :
    Nat.card F + Nat.card (Γ.supportGraph O).ConnectedComponent = Nat.card Γ.V := by
  have hcard := hF.bijOn_endpoints.ncard_eq
  have hcomp := Nat.card_congr
    ((Γ.supportGraph F).connectedComponentEquivOfReachableEq hF.reachable_eq)
  have h := hF.isAcyclic.ncard_edgeSet_add_card_connectedComponent
  simpa only [Nat.card_coe_set_eq, ← hcard, hcomp] using h

end TauCeti.SerreGraph
