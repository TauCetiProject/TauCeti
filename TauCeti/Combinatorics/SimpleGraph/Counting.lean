/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm

/-!
# Counting graph homomorphisms

Cardinality bounds for homomorphisms and injective homomorphisms between finite simple graphs.
These compare graph homomorphism counts with all vertex maps and embeddings, enabling the
normalization and estimates used for finite homomorphism densities.
The cardinality bounds use `Nat.card` and need only `Finite` vertex types, without chosen
enumerations. The sum and labelled-copy-count formulas use `Fintype` as required by their
right-hand sides.

## Main results

* `SimpleGraph.card_hom_le` bounds homomorphisms by all vertex maps.
* `SimpleGraph.card_injective_hom_le` bounds injective homomorphisms by vertex embeddings.
* `SimpleGraph.card_injective_hom_eq_sum_map_le` counts injective homomorphisms by the vertex
  embeddings whose mapped graph lies below the target.
* `SimpleGraph.card_hom_eq_card_adjPreservingMaps` counts homomorphisms by the
  adjacency-preserving vertex maps.
* `SimpleGraph.card_injective_hom_eq_labelledCopyCount` identifies the number of injective
  homomorphisms with Mathlib's `SimpleGraph.labelledCopyCount`, so injective homomorphism counts
  and labelled copy counts are one counting convention, not two.

The extreme patterns and hosts are counted exactly. Every vertex map out of the edgeless graph is a
homomorphism, and every vertex embedding into the complete graph is one. A homomorphism out of the
complete graph on `V` is injective, and its image is a `card V`-clique; each clique arises from
`(card V)!` such maps. For the edge `K₂` these maps are the darts of the host.

* `SimpleGraph.card_bot_hom` counts the homomorphisms out of the edgeless graph.
* `SimpleGraph.card_injective_hom_top` counts the injective homomorphisms into the complete graph.
* `SimpleGraph.card_injective_top_hom` identifies the injective homomorphisms out of the complete
  graph with all of them.
* `SimpleGraph.labelledCopyCount_top` and `SimpleGraph.card_top_hom` count the copies of, and the
  homomorphisms from, a complete graph by the cliques of the host.
* `SimpleGraph.card_top_fin_two_hom` counts the homomorphisms from `K₂` by the edges of the host.
-/

public section

open Finset

namespace SimpleGraph

variable {V W : Type*}

/-- Homomorphisms and adjacency-preserving vertex maps are counted alike. -/
theorem card_hom_eq_card_adjPreservingMaps (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card (F →g G) = Nat.card {ψ : V → W // ∀ a b, F.Adj a b → G.Adj (ψ a) (ψ b)} :=
  Nat.card_congr
    { toFun := fun φ => ⟨⇑φ, fun _ _ h => φ.map_rel h⟩
      invFun := fun ψ => ⟨ψ.1, fun {_ _} h => ψ.2 _ _ h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Every homomorphism out of a complete graph is injective, so the injective homomorphisms from
the complete graph on `V` are all of them. -/
theorem card_injective_top_hom (G : SimpleGraph W) :
    Nat.card {φ : (⊤ : SimpleGraph V) →g G // Function.Injective φ} =
      Nat.card ((⊤ : SimpleGraph V) →g G) :=
  Nat.card_congr (Equiv.subtypeUnivEquiv Hom.injective_of_top_hom)

section CardinalityBounds

variable [Finite V] [Finite W]

/-- The number of homomorphisms from `F` to `G` is bounded by the number of vertex maps. -/
theorem card_hom_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card (F →g G) ≤ Nat.card W ^ Nat.card V := by
  calc Nat.card (F →g G) ≤ Nat.card (V → W) :=
        Nat.card_le_card_of_injective (fun φ => (φ : V → W))
          (fun a b h => by ext x; exact congrFun h x)
    _ = Nat.card W ^ Nat.card V := Nat.card_fun

/-- The number of injective homomorphisms from `F` to `G` is bounded by the number of embeddings
of the vertex types. -/
theorem card_injective_hom_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card {φ : F →g G // Function.Injective φ}
      ≤ (Nat.card W).descFactorial (Nat.card V) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite W
  calc Nat.card {φ : F →g G // Function.Injective φ} ≤ Nat.card (V ↪ W) :=
        Nat.card_le_card_of_injective (fun φ => ⟨(φ.1 : V → W), φ.2⟩)
          (fun a b h => by
            ext x; exact congrFun (congrArg (fun e : V ↪ W => (e : V → W)) h) x)
    _ = (Nat.card W).descFactorial (Nat.card V) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
        simp only [Nat.card_eq_fintype_card]

end CardinalityBounds

variable [Fintype V] [Fintype W]

/-- The number of injective homomorphisms from `F` to `G` is Mathlib's labelled copy count.

`SimpleGraph.Copy F G` is definitionally an injective homomorphism, so this is an equivalence of
subtypes. Mathlib takes the host graph first: `G.labelledCopyCount F` counts copies of `F` inside
`G`.

Deliberately not `@[simp]`: the left-hand side is not in simp normal form, since `Nat.card` of a
`Fintype` rewrites to `Fintype.card`. -/
theorem card_injective_hom_eq_labelledCopyCount (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card {φ : F →g G // Function.Injective φ} = G.labelledCopyCount F := by
  -- `labelledCopyCount` is defined by `classical exact Fintype.card (Copy H G)`, so unfolding it
  -- exposes a `Fintype (Copy F G)` that only `classical` provides.
  classical
  rw [labelledCopyCount, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun φ => ⟨φ.1, φ.2⟩
      invFun := fun c => ⟨c.toHom, c.injective'⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open Classical in
/-- Injective graph homomorphisms are counted by the vertex embeddings whose mapped graph lies
below the host graph. -/
theorem card_injective_hom_eq_sum_map_le (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card {φ : F →g G // Function.Injective φ} =
      ∑ f : V ↪ W, if F.map f ≤ G then 1 else 0 := by
  let e : {φ : F →g G // Function.Injective φ} ≃ {f : V ↪ W // F.map f ≤ G} :=
    { toFun := fun φ =>
        ⟨⟨φ.1, φ.2⟩, map_le_iff_le_comap.2 fun {_ _} hab => φ.1.map_rel hab⟩
      invFun := fun f =>
        ⟨⟨f.1, fun {_ _} hab => map_le_iff_le_comap.1 f.2 hab⟩, f.1.injective⟩
      left_inv := by
        intro φ
        apply Subtype.ext
        exact RelHom.ext fun _ => rfl
      right_inv := by
        intro f
        apply Subtype.ext
        exact DFunLike.ext _ _ fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

/-! ### Complete and edgeless graphs -/

/-- Homomorphisms out of the edgeless graph are all vertex maps. -/
theorem card_bot_hom (G : SimpleGraph W) :
    Nat.card ((⊥ : SimpleGraph V) →g G) = Fintype.card W ^ Fintype.card V := by
  rw [card_hom_eq_card_adjPreservingMaps,
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ _ _ h => h.elim), Nat.card_fun,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- Injective homomorphisms into the complete graph are all vertex embeddings, counted by the
falling factorial. -/
theorem card_injective_hom_top (F : SimpleGraph V) :
    Nat.card {φ : F →g (⊤ : SimpleGraph W) // Function.Injective φ} =
      (Fintype.card W).descFactorial (Fintype.card V) := by
  rw [← Fintype.card_embedding_eq, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun φ => ⟨φ.1, φ.2⟩
      invFun := fun f => ⟨⟨f, fun {_ _} h => f.injective.ne h.ne⟩, f.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

section Clique

variable [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

/-- The labelled copies of the complete graph on `V` in `G` are the orderings of the
`card V`-cliques of `G` by `V`, so there are `(card V)!` of them for each clique. -/
theorem labelledCopyCount_top :
    G.labelledCopyCount (⊤ : SimpleGraph V) =
      (Fintype.card V).factorial * #(G.cliqueFinset (Fintype.card V)) := by
  classical
  -- Sort the copies by their vertex sets, which are the `card V`-cliques of `G`.
  let f (c : Copy (⊤ : SimpleGraph V) G) : G.cliqueFinset (Fintype.card V) :=
    ⟨Finset.univ.map c.toEmbedding, G.mem_cliqueFinset_iff.2 (isNClique_map_copy_top c)⟩
  -- The copies with vertex set `S` are the bijections from `V` onto `S`.
  have hfib (S : G.cliqueFinset (Fintype.card V)) : {c // f c = S} ≃ (V ≃ S.1) :=
    { toFun := fun c =>
        have hc : (f c.1).1 = S.1 := congrArg Subtype.val c.2
        Equiv.ofBijective
          (fun v => ⟨c.1 v, by rw [← hc]; exact Finset.mem_map_of_mem _ (Finset.mem_univ v)⟩)
          ⟨fun v w h => c.1.injective (congrArg Subtype.val h), fun x => by
            obtain ⟨v, -, hv⟩ := Finset.mem_map.1 (by rw [hc]; exact x.2 : x.1 ∈ (f c.1).1)
            exact ⟨v, Subtype.ext hv⟩⟩
      invFun := fun e => ⟨⟨⟨fun v => (e v).1, fun {v w} hvw =>
          (G.isClique_iff.1 (G.mem_cliqueFinset_iff.1 S.2).isClique) (e v).2 (e w).2
            fun h => hvw.ne (e.injective (Subtype.ext h))⟩,
          fun v w h => e.injective (Subtype.ext h)⟩, Subtype.ext <| Finset.ext fun x =>
            ⟨fun hx => by
              obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 hx
              exact (e v).2,
            fun hx => Finset.mem_map.2 ⟨e.symm ⟨x, hx⟩, Finset.mem_univ _,
              congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Equiv.ext fun _ => rfl }
  have hcard (S : G.cliqueFinset (Fintype.card V)) :
      Nat.card {c // f c = S} = (Fintype.card V).factorial := by
    have hS : Fintype.card V = Fintype.card S.1 := by
      rw [Fintype.card_coe, (G.mem_cliqueFinset_iff.1 S.2).card_eq]
    rw [Nat.card_congr (hfib S), Nat.card_eq_fintype_card,
      Fintype.card_equiv (Fintype.equivOfCardEq hS)]
  have key : Nat.card (Copy (⊤ : SimpleGraph V) G) =
      (Fintype.card V).factorial * #(G.cliqueFinset (Fintype.card V)) := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_comm]
  rw [labelledCopyCount, Fintype.card_eq_nat_card, key]

/-- Every homomorphism out of a complete graph is injective, so the homomorphisms from the complete
graph on `V` to `G` are again counted by `(card V)!` orderings of each `card V`-clique of `G`. -/
theorem card_top_hom :
    Nat.card ((⊤ : SimpleGraph V) →g G) =
      (Fintype.card V).factorial * #(G.cliqueFinset (Fintype.card V)) := by
  rw [← card_injective_top_hom, card_injective_hom_eq_labelledCopyCount, labelledCopyCount_top]

end Clique

/-- The homomorphisms from `K₂` to `G` are the darts of `G`, twice as many as its edges. -/
theorem card_top_fin_two_hom (G : SimpleGraph W) [DecidableRel G.Adj] :
    Nat.card ((⊤ : SimpleGraph (Fin 2)) →g G) = 2 * #G.edgeFinset := by
  rw [← dart_card_eq_twice_card_edges, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun φ => ⟨(φ 0, φ 1), φ.map_rel (by decide)⟩
      invFun := fun d => ⟨![d.fst, d.snd], fun {i j} h => ?_⟩
      left_inv := fun φ => ?_
      right_inv := fun _ => rfl }
  · fin_cases i <;> fin_cases j
    exacts [(h rfl).elim, d.adj, d.adj.symm, (h rfl).elim]
  · ext i
    fin_cases i <;> rfl

end SimpleGraph
