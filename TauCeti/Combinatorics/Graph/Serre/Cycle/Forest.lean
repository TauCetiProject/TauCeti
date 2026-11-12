/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Path.Basic
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

Two vertices are joined in the simple support of a reversal-closed set of darts exactly when a
path through those darts joins them. In particular, the simple support of an orientation has
the connectivity of the graph.

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

variable {Γ O} in
/-- A chosen dart that is not a loop joins its endpoints in the simple support. -/
theorem supportGraph_adj_src_tgt {e : Γ.E} (he : e ∈ O) (hne : Γ.src e ≠ Γ.tgt e) :
    (Γ.supportGraph O).Adj (Γ.src e) (Γ.tgt e) :=
  (Γ.supportGraph_adj O _ _).mpr ⟨hne, .inl ⟨e, he, rfl, rfl⟩⟩

/-- The simple support has no edges exactly when every chosen dart is a loop. -/
theorem supportGraph_eq_bot_iff : Γ.supportGraph O = ⊥ ↔ ∀ e ∈ O, Γ.src e = Γ.tgt e := by
  refine ⟨fun h e he => by_contra fun hne => ?_, fun h => ?_⟩
  · simpa [h] using supportGraph_adj_src_tgt he hne
  · ext x y
    simp only [supportGraph_adj, SimpleGraph.bot_adj, iff_false]
    rintro ⟨hxy, ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩⟩
    exacts [hxy (h e he), hxy (h e he).symm]

/-- The simple support of a single dart is the single edge joining its endpoints; it has no
edge when the dart is a loop. -/
theorem supportGraph_singleton (e : Γ.E) :
    Γ.supportGraph {e} = SimpleGraph.edge (Γ.src e) (Γ.tgt e) := by
  ext x y
  simp only [supportGraph_adj, Set.mem_singleton_iff, exists_eq_left, SimpleGraph.edge_adj]
  tauto

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

/-- The empty set of darts is a spanning forest exactly when every chosen dart is a loop:
isolated vertices and loops need no forest edge, and any other dart needs one. -/
theorem isSpanningForest_empty_iff : Γ.IsSpanningForest O ∅ ↔ ∀ e ∈ O, Γ.src e = Γ.tgt e := by
  rw [← supportGraph_eq_bot_iff]
  refine ⟨fun hF => ?_, fun h => ⟨Set.empty_subset O, by simp, Set.injOn_empty _, by simp,
    by rw [h, supportGraph_empty]⟩⟩
  ext x y
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hxy
  have hreach := hxy.reachable
  rw [← hF.reachable_eq, supportGraph_empty, SimpleGraph.reachable_bot] at hreach
  exact hxy.ne hreach

/-- When every chosen dart is a loop, the only spanning forest is the empty one: a spanning
forest never contains a loop. -/
theorem IsSpanningForest.eq_empty (hF : Γ.IsSpanningForest O F)
    (h : ∀ e ∈ O, Γ.src e = Γ.tgt e) : F = ∅ :=
  Set.eq_empty_of_forall_notMem fun e he => hF.src_ne_tgt e he (h e (hF.subset he))

/-- A dart that is not a loop is a spanning forest of any family of darts whose members are
loops or join the same two vertices, in either direction. This covers a bundle of parallel
edges together with loops at their endpoints, with no restriction on the other vertices. -/
theorem isSpanningForest_singleton {e : Γ.E} (he : e ∈ O) (hne : Γ.src e ≠ Γ.tgt e)
    (hO : ∀ f ∈ O, Γ.src f ≠ Γ.tgt f → s(Γ.src f, Γ.tgt f) = s(Γ.src e, Γ.tgt e)) :
    Γ.IsSpanningForest O {e} := by
  have hsupport : Γ.supportGraph {e} = Γ.supportGraph O := by
    apply SimpleGraph.edgeSet_injective
    rw [supportGraph_edgeSet, supportGraph_edgeSet]
    ext q
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨by rintro ⟨f, ⟨rfl, hf⟩, rfl⟩; exact ⟨f, ⟨he, hf⟩, rfl⟩,
      by rintro ⟨f, ⟨hfO, hf⟩, rfl⟩; exact ⟨e, ⟨rfl, hne⟩, (hO f hfO hf).symm⟩⟩
  have hacyc : (Γ.supportGraph {e}).IsAcyclic := by
    have h : (⊥ ⊔ SimpleGraph.edge (Γ.src e) (Γ.tgt e)).IsAcyclic :=
      SimpleGraph.isAcyclic_sup_fromEdgeSet_iff.mpr
        ⟨SimpleGraph.isAcyclic_bot, fun h => .inl (SimpleGraph.reachable_bot.mp h)⟩
    rwa [bot_sup_eq, ← supportGraph_singleton] at h
  exact ⟨Set.singleton_subset_iff.mpr he, by simpa using hne, Set.injOn_singleton _ _, hacyc,
    by rw [hsupport]⟩

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
theorem IsSpanningForest.card_add_card_connectedComponent [Finite Γ.V]
    (hF : Γ.IsSpanningForest O F) :
    Nat.card F + Nat.card (Γ.supportGraph O).ConnectedComponent = Nat.card Γ.V := by
  have hcard := hF.bijOn_endpoints.ncard_eq
  have hcomp := Nat.card_congr
    ((Γ.supportGraph F).connectedComponentEquivOfReachableEq hF.reachable_eq)
  have h := hF.isAcyclic.ncard_edgeSet_add_card_connectedComponent
  simpa only [Nat.card_coe_set_eq, ← hcard, hcomp] using h

/-- When every chosen dart is a loop, each vertex is its own component. In particular this
counts the components of a graph without edges. -/
theorem card_connectedComponent_supportGraph_of_forall_src_eq_tgt
    (h : ∀ e ∈ O, Γ.src e = Γ.tgt e) :
    Nat.card (Γ.supportGraph O).ConnectedComponent = Nat.card Γ.V := by
  rw [(Γ.supportGraph_eq_bot_iff O).mpr h]
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨fun _ _ hab =>
    SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.exact hab),
    Quot.mk_surjective⟩)).symm

/-! ### Reachability in the simple support -/

/-- The endpoints of a path are joined in the simple support of any set of darts containing the
darts of the path. -/
theorem Path.reachable_supportGraph {S : Set Γ.E} {a b : Γ.V} (p : Γ.Path a b)
    (hp : ∀ e ∈ Path.darts Γ p, e ∈ S) : (Γ.supportGraph S).Reachable a b := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
    refine (ih fun f hf => hp f (by simp [hf])).trans ?_
    rcases eq_or_ne b c with rfl | hbc
    · rfl
    · exact SimpleGraph.Adj.reachable
        ((Γ.supportGraph_adj S b c).mpr ⟨hbc, .inl ⟨e.1, hp e.1 (by simp), e.2⟩⟩)

/-- Two vertices are joined in the simple support of a reversal-closed set of darts exactly when
they are joined by a path through those darts. -/
theorem reachable_supportGraph_iff {S : Set Γ.E} (hS : ∀ e ∈ S, Γ.rev e ∈ S) {a b : Γ.V} :
    (Γ.supportGraph S).Reachable a b ↔ ∃ p : Γ.Path a b, ∀ e ∈ Path.darts Γ p, e ∈ S := by
  refine ⟨fun h => ?_, fun ⟨p, hp⟩ => p.reachable_supportGraph hp⟩
  replace h := (SimpleGraph.reachable_iff_reflTransGen a b).mp h
  induction h with
  | refl => exact ⟨.nil, by simp⟩
  | tail _ hadj ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨e, he, rfl, rfl⟩ : ∃ e ∈ S, Γ.src e = _ ∧ Γ.tgt e = _ := by
      obtain ⟨-, ⟨e, he, h₁, h₂⟩ | ⟨e, he, h₁, h₂⟩⟩ := (Γ.supportGraph_adj S _ _).mp hadj
      · exact ⟨e, he, h₁, h₂⟩
      · exact ⟨Γ.rev e, hS e he, by simpa using h₂, by simpa using h₁⟩
    refine ⟨p.cons (Γ.dart e), ?_⟩
    simp only [Path.darts_cons, List.mem_append, List.mem_singleton, dart_val]
    rintro f (hf | rfl)
    exacts [hp f hf, he]

/-- The positive darts of a reversal-closed set of darts have the same simple support as the
whole set. -/
theorem IsOrientation.supportGraph_inter (hO : Γ.IsOrientation O) {S : Set Γ.E}
    (hS : ∀ e ∈ S, Γ.rev e ∈ S) : Γ.supportGraph (S ∩ O) = Γ.supportGraph S := by
  have key : ∀ x y, ∀ e ∈ S, x ≠ y → Γ.src e = x → Γ.tgt e = y →
      (Γ.supportGraph (S ∩ O)).Adj x y := by
    intro x y e he hne h₁ h₂
    refine (Γ.supportGraph_adj _ x y).mpr ⟨hne, ?_⟩
    by_cases heO : e ∈ O
    · exact .inl ⟨e, ⟨he, heO⟩, h₁, h₂⟩
    · exact .inr ⟨Γ.rev e, ⟨hS e he, (hO.mem_rev_iff Γ e).mpr heO⟩, by simpa using h₂,
        by simpa using h₁⟩
  refine le_antisymm (Γ.supportGraph_mono Set.inter_subset_left) fun x y hxy => ?_
  obtain ⟨hne, ⟨e, he, h₁, h₂⟩ | ⟨e, he, h₁, h₂⟩⟩ := (Γ.supportGraph_adj S x y).mp hxy
  · exact key x y e he hne h₁ h₂
  · exact (key y x e he hne.symm h₁ h₂).symm

/-- Two vertices are joined in the simple support of an orientation exactly when they are
joined by a path of the graph. -/
theorem IsOrientation.reachable_supportGraph_iff (hO : Γ.IsOrientation O) {a b : Γ.V} :
    (Γ.supportGraph O).Reachable a b ↔ Nonempty (Γ.Path a b) := by
  rw [← Set.univ_inter O, hO.supportGraph_inter fun _ _ => Set.mem_univ _,
    SerreGraph.reachable_supportGraph_iff fun _ _ => Set.mem_univ _]
  exact ⟨fun ⟨p, _⟩ => ⟨p⟩, fun ⟨p⟩ => ⟨p, fun _ _ => Set.mem_univ _⟩⟩

/-- The simple support of an orientation is connected exactly when the graph is. -/
theorem IsOrientation.connected_supportGraph_iff (hO : Γ.IsOrientation O) :
    (Γ.supportGraph O).Connected ↔ Γ.Connected := by
  simp only [SimpleGraph.connected_iff, SimpleGraph.Preconnected, hO.reachable_supportGraph_iff,
    connected_iff, preconnected_iff, and_comm]

end TauCeti.SerreGraph
