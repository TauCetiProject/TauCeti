/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
public import TauCeti.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Positivity

/-!
# Homomorphism densities of uniform hypergraphs

A vertex map `f : U → V` is a homomorphism from an `r`-uniform hypergraph `F` to an `r`-uniform
hypergraph `H` when it maps every edge of `F` onto an edge of `H`
(`TauCeti.UniformHypergraph.IsHom`). Since both edges have `r` vertices, a homomorphism is
injective on every edge of `F`. This file counts homomorphisms and
injective homomorphisms between uniform hypergraphs on finite vertex types, and normalizes the
counts to densities:

* `F.homDensity H = #Hom(F, H) / |V| ^ |U|`, the proportion of all vertex maps that are
  homomorphisms;
* `F.injHomDensity H = #Inj(F, H) / (|V|)_{|U|}`, the proportion of all vertex embeddings that are
  homomorphisms, normalized by the falling factorial `(|V|)_{|U|} = (Fintype.card V).descFactorial
  (Fintype.card U)`.

Both densities lie in `[0, 1]` and are rational, like the edge density of
`TauCeti.UniformHypergraph`.
When the host is empty and the pattern is not, the denominator vanishes and the densities are `0`.

The empty pattern has density `1` in every nonempty host, and every pattern has injective density
`1` in a complete host with at least as many vertices. A single edge, the complete `r`-uniform
hypergraph on `r` vertices, has homomorphism count `r! · #H.edges`, so its injective density is
the edge density of `H`.

For simple graphs, regarded as `2`-uniform hypergraphs through `SimpleGraph.toUniformHypergraph`,
hypergraph homomorphisms are exactly graph homomorphisms. The two densities therefore agree with
`TauCeti.DenseGraphLimits.homDensityFin` and `TauCeti.DenseGraphLimits.injHomDensity`, and the
injective count is Mathlib's labelled copy count `SimpleGraph.labelledCopyCount`.

## Main definitions

* `TauCeti.UniformHypergraph.homCount` and `TauCeti.UniformHypergraph.injHomCount`: the numbers of
  homomorphisms and of injective homomorphisms.
* `TauCeti.UniformHypergraph.homDensity` and `TauCeti.UniformHypergraph.injHomDensity`: the
  corresponding densities.

## Main results

* `TauCeti.UniformHypergraph.homDensity_le_one` and
  `TauCeti.UniformHypergraph.injHomDensity_le_one`: both densities are at most `1`.
* `TauCeti.UniformHypergraph.homDensity_empty_left` and
  `TauCeti.UniformHypergraph.injHomDensity_complete_right`: the two normalizations are exact.
* `TauCeti.UniformHypergraph.injHomDensity_complete_left_of_card_eq`: the injective density of a
  single edge is the edge density.
* `SimpleGraph.homDensity_toUniformHypergraph` and
  `SimpleGraph.injHomDensity_toUniformHypergraph`: agreement with the graph densities.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §5.2.
-/

public section

open Finset

namespace TauCeti

namespace UniformHypergraph

variable {r : ℕ} {U V : Type*}

/-! ### Counting homomorphisms -/

section Count

variable [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
  {F : UniformHypergraph r U} {H : UniformHypergraph r V}

/-- The number of homomorphisms from `F` to `H`. -/
def homCount (F : UniformHypergraph r U) (H : UniformHypergraph r V) : ℕ :=
  #{f : U → V | F.IsHom H f}

/-- The number of injective homomorphisms from `F` to `H`, counted as vertex embeddings. -/
noncomputable def injHomCount (F : UniformHypergraph r U) (H : UniformHypergraph r V) : ℕ :=
  #{f : U ↪ V | F.IsHom H f}

/-- The homomorphisms are counted among all vertex maps. -/
theorem homCount_def (F : UniformHypergraph r U) (H : UniformHypergraph r V) :
    F.homCount H = #{f : U → V | F.IsHom H f} := (rfl)

omit [DecidableEq U] in
/-- The injective homomorphisms are counted among all vertex embeddings. -/
theorem injHomCount_def (F : UniformHypergraph r U) (H : UniformHypergraph r V) :
    F.injHomCount H = #{f : U ↪ V | F.IsHom H f} := (rfl)

/-- There are at most `|V| ^ |U|` homomorphisms, one for each vertex map at most. -/
theorem homCount_le : F.homCount H ≤ Fintype.card V ^ Fintype.card U :=
  (card_filter_le _ _).trans_eq (by rw [card_univ, Fintype.card_fun])

omit [DecidableEq U] in
/-- There are at most `(|V|)_{|U|}` injective homomorphisms, one for each vertex embedding at
most. -/
theorem injHomCount_le : F.injHomCount H ≤ (Fintype.card V).descFactorial (Fintype.card U) :=
  (card_filter_le _ _).trans_eq (by rw [card_univ, Fintype.card_embedding_eq])

/-- Injective homomorphisms are homomorphisms. -/
theorem injHomCount_le_homCount : F.injHomCount H ≤ F.homCount H :=
  card_le_card_of_injOn (⇑) (fun f hf ↦ by simpa using hf)
    (fun _ _ _ _ h ↦ DFunLike.coe_injective h)

/-- When every homomorphism is injective, the two counts agree. -/
theorem injHomCount_eq_homCount (h : ∀ f : U → V, F.IsHom H f → Function.Injective f) :
    F.injHomCount H = F.homCount H :=
  card_nbij (⇑) (fun f hf ↦ by simpa using hf) (fun _ _ _ _ h ↦ DFunLike.coe_injective h)
    fun f hf ↦ by
      have hf : F.IsHom H f := (mem_filter.1 hf).2
      exact ⟨⟨f, h f hf⟩, by simpa using hf, rfl⟩

/-- Every vertex map is a homomorphism out of the empty hypergraph. -/
@[simp]
theorem homCount_empty_left : (empty r U).homCount H = Fintype.card V ^ Fintype.card U := by
  simp [homCount_def]

omit [DecidableEq U] in
/-- Every vertex embedding is an injective homomorphism out of the empty hypergraph. -/
@[simp]
theorem injHomCount_empty_left :
    (empty r U).injHomCount H = (Fintype.card V).descFactorial (Fintype.card U) := by
  simp [injHomCount_def, Fintype.card_embedding_eq]

/-- A pattern with an edge has no homomorphism into the empty hypergraph. -/
@[simp]
theorem homCount_empty_right (hF : F.edges.Nonempty) : F.homCount (empty r V) = 0 := by
  simp [homCount_def, hF.ne_empty]

omit [DecidableEq U] in
/-- A pattern with an edge has no injective homomorphism into the empty hypergraph. -/
@[simp]
theorem injHomCount_empty_right (hF : F.edges.Nonempty) : F.injHomCount (empty r V) = 0 := by
  simp [injHomCount_def, hF.ne_empty]

omit [DecidableEq U] in
/-- Every vertex embedding is a homomorphism into the complete hypergraph. -/
@[simp]
theorem injHomCount_complete_right :
    F.injHomCount (complete r V) = (Fintype.card V).descFactorial (Fintype.card U) := by
  rw [injHomCount_def, filter_true_of_mem fun f _ ↦ isHom_complete_right_of_injective f.injective,
    card_univ, Fintype.card_embedding_eq]

omit [DecidableEq U] in
/-- The injective homomorphisms out of a single edge, the complete `r`-uniform hypergraph on `r`
vertices, are the orderings of the edges of the host: there are `r!` for each edge. -/
theorem injHomCount_complete_left_of_card_eq (hU : Fintype.card U = r) :
    (complete r U).injHomCount H = r.factorial * #H.edges := by
  have hedges : (complete r U).edges = {univ} := by
    ext e
    rw [mem_edges_complete, mem_singleton, ← hU, card_eq_iff_eq_univ]
  have huniv (f : U ↪ V) : (complete r U).IsHom H f ↔ univ.map f ∈ H.edges := by
    simp [isHom_iff, hedges, map_eq_image]
  simp_rw [injHomCount_def, huniv]
  -- Sort the embeddings by the edge onto which they map the vertices of the pattern.
  refine (card_eq_sum_card_fiberwise (f := fun f : U ↪ V ↦ univ.map f) (t := H.edges)
    fun f hf ↦ (mem_filter.1 hf).2).trans ?_
  rw [sum_congr rfl fun e he ↦ ?_, sum_const, smul_eq_mul, mul_comm]
  have hcard : #e = Fintype.card U := by rw [H.edge_card e he, hU]
  -- An embedding maps the `|U|` vertices onto the edge `e` exactly when it maps them into `e`.
  trans #{f : U ↪ V | ∀ u, f u ∈ e}
  · congr 1
    ext f
    simp only [mem_filter, mem_univ, mem_coe, true_and]
    refine ⟨fun ⟨_, hf⟩ u ↦ hf ▸ mem_map_of_mem f (mem_univ u), fun hf ↦ ?_⟩
    have hfe : univ.map f = e := eq_of_subset_of_card_le
      (fun x hx ↦ by obtain ⟨u, -, rfl⟩ := mem_map.1 hx; exact hf u)
      (by rw [card_map, card_univ, hcard])
    exact ⟨hfe ▸ he, hfe⟩
  -- These are the orderings of `e` by `U`.
  have hocc : Function.occCount (fun _ : U ↦ e) e = Fintype.card U := by
    rw [Function.occCount_eq_card_filter, filter_true_of_mem fun _ _ ↦ rfl, card_univ]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Nat.card_embedding_mem_eq_prod_descFactorial (fun _ ↦ e) (fun _ ↦ mem_singleton_self e)
      (by simp), prod_singleton, hocc, hcard, Nat.descFactorial_self, hU]

/-- The homomorphisms out of a single edge, the complete `r`-uniform hypergraph on `r` vertices,
are the orderings of the edges of the host: there are `r!` for each edge. -/
theorem homCount_complete_left_of_card_eq (hU : Fintype.card U = r) :
    (complete r U).homCount H = r.factorial * #H.edges := by
  rw [← injHomCount_eq_homCount fun _ ↦ injective_of_isHom_complete hU,
    injHomCount_complete_left_of_card_eq hU]

/-! ### Densities -/

/-- The **homomorphism density** `t(F, H) = #Hom(F, H) / |V| ^ |U|`: the proportion of vertex maps
`U → V` that are homomorphisms from `F` to `H`. -/
def homDensity (F : UniformHypergraph r U) (H : UniformHypergraph r V) : ℚ :=
  (F.homCount H : ℚ) / (Fintype.card V ^ Fintype.card U : ℚ)

/-- The **injective homomorphism density** `t₀(F, H) = #Inj(F, H) / (|V|)_{|U|}`: the proportion of
vertex embeddings `U ↪ V` that are homomorphisms from `F` to `H`, normalized by the falling
factorial `(|V|)_{|U|}`. -/
noncomputable def injHomDensity (F : UniformHypergraph r U) (H : UniformHypergraph r V) : ℚ :=
  (F.injHomCount H : ℚ) / ((Fintype.card V).descFactorial (Fintype.card U) : ℚ)

/-- The homomorphism density is the homomorphism count over `|V| ^ |U|`. -/
theorem homDensity_def (F : UniformHypergraph r U) (H : UniformHypergraph r V) :
    F.homDensity H = (F.homCount H : ℚ) / (Fintype.card V ^ Fintype.card U : ℚ) := (rfl)

omit [DecidableEq U] in
/-- The injective homomorphism density is the injective homomorphism count over `(|V|)_{|U|}`. -/
theorem injHomDensity_def (F : UniformHypergraph r U) (H : UniformHypergraph r V) :
    F.injHomDensity H =
      (F.injHomCount H : ℚ) / ((Fintype.card V).descFactorial (Fintype.card U) : ℚ) := (rfl)

/-- The homomorphism density is nonnegative. -/
theorem homDensity_nonneg : 0 ≤ F.homDensity H := by
  rw [homDensity_def]
  positivity

omit [DecidableEq U] in
/-- The injective homomorphism density is nonnegative. -/
theorem injHomDensity_nonneg : 0 ≤ F.injHomDensity H := by
  rw [injHomDensity_def]
  positivity

/-- The homomorphism density is at most `1`. When the host is empty and the pattern is not, both
the count and the denominator vanish, and the density is `0`. -/
theorem homDensity_le_one : F.homDensity H ≤ 1 := by
  rw [homDensity_def]
  exact div_le_one_of_le₀ (by exact_mod_cast (homCount_le (F := F) (H := H))) (by positivity)

omit [DecidableEq U] in
/-- The injective homomorphism density is at most `1`. When the host has fewer vertices than the
pattern, both the count and the falling factorial vanish, and the density is `0`. -/
theorem injHomDensity_le_one : F.injHomDensity H ≤ 1 := by
  rw [injHomDensity_def]
  exact div_le_one_of_le₀ (by exact_mod_cast (injHomCount_le (F := F) (H := H))) (by positivity)

/-- The empty pattern has homomorphism density `1` in every nonempty host: every vertex map is a
homomorphism, and the power `|V| ^ |U|` counts them. -/
@[simp]
theorem homDensity_empty_left [Nonempty V] : (empty r U).homDensity H = 1 := by
  rw [homDensity_def, homCount_empty_left, Nat.cast_pow]
  exact div_self (pow_ne_zero _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero))

omit [DecidableEq U] in
/-- The empty pattern has injective homomorphism density `1` in every host with at least as many
vertices: every vertex embedding is a homomorphism. -/
@[simp]
theorem injHomDensity_empty_left (h : Fintype.card U ≤ Fintype.card V) :
    (empty r U).injHomDensity H = 1 := by
  rw [injHomDensity_def, injHomCount_empty_left]
  exact div_self (Nat.cast_ne_zero.2 (Nat.descFactorial_eq_zero_iff_lt.not.2 h.not_gt))

/-- A pattern with an edge has homomorphism density `0` in the empty hypergraph. -/
@[simp]
theorem homDensity_empty_right (hF : F.edges.Nonempty) : F.homDensity (empty r V) = 0 := by
  rw [homDensity_def, homCount_empty_right hF, Nat.cast_zero, zero_div]

omit [DecidableEq U] in
/-- A pattern with an edge has injective homomorphism density `0` in the empty hypergraph. -/
@[simp]
theorem injHomDensity_empty_right (hF : F.edges.Nonempty) : F.injHomDensity (empty r V) = 0 := by
  rw [injHomDensity_def, injHomCount_empty_right hF, Nat.cast_zero, zero_div]

omit [DecidableEq U] in
/-- Every pattern has injective homomorphism density `1` in a complete host with at least as many
vertices: every vertex embedding is a homomorphism, and the falling factorial `(|V|)_{|U|}` counts
them. -/
@[simp]
theorem injHomDensity_complete_right (h : Fintype.card U ≤ Fintype.card V) :
    F.injHomDensity (complete r V) = 1 := by
  rw [injHomDensity_def, injHomCount_complete_right]
  exact div_self (Nat.cast_ne_zero.2 (Nat.descFactorial_eq_zero_iff_lt.not.2 h.not_gt))

/-- The homomorphism density of a single edge, the complete `r`-uniform hypergraph on `r`
vertices: `r!` orderings of each edge of the host, out of `|V| ^ r` vertex maps. -/
theorem homDensity_complete_left_of_card_eq (hU : Fintype.card U = r) :
    (complete r U).homDensity H = r.factorial * #H.edges / (Fintype.card V ^ r : ℚ) := by
  rw [homDensity_def, homCount_complete_left_of_card_eq hU, hU, Nat.cast_mul]

omit [DecidableEq U] in
/-- The injective homomorphism density of a single edge, the complete `r`-uniform hypergraph on
`r` vertices, is the edge density of the host: the falling factorial `(|V|)_r` is `r!` times the
number `(|V|).choose r` of possible edges. -/
theorem injHomDensity_complete_left_of_card_eq (hU : Fintype.card U = r) :
    (complete r U).injHomDensity H = H.edgeDensity := by
  rw [injHomDensity_def, injHomCount_complete_left_of_card_eq hU, edgeDensity_def, hU,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r))

end Count

end UniformHypergraph

/-! ### Simple graphs as `2`-uniform hypergraphs -/

section SimpleGraph

open UniformHypergraph

variable {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
  (F : SimpleGraph U) (G : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel G.Adj]

variable {F G} in
/-- A vertex map is a homomorphism between the `2`-uniform hypergraphs of two simple graphs
exactly when it maps adjacent vertices to adjacent vertices. -/
theorem _root_.SimpleGraph.isHom_toUniformHypergraph_iff {f : U → V} :
    F.toUniformHypergraph.IsHom G.toUniformHypergraph f ↔
      ∀ a b, F.Adj a b → G.Adj (f a) (f b) := by
  refine ⟨fun h a b hab ↦ ?_, fun h ↦ isHom_iff.2 fun e he ↦ ?_⟩
  · have hmem := h.image_mem (SimpleGraph.insert_mem_toUniformHypergraph_edges.2 hab)
    rwa [image_insert, image_singleton, SimpleGraph.insert_mem_toUniformHypergraph_edges] at hmem
  · obtain ⟨a, b, -, rfl⟩ := card_eq_two.1 (F.toUniformHypergraph.edge_card e he)
    rw [image_insert, image_singleton, SimpleGraph.insert_mem_toUniformHypergraph_edges]
    exact h a b (SimpleGraph.insert_mem_toUniformHypergraph_edges.1 he)

/-- The homomorphisms between the `2`-uniform hypergraphs of two simple graphs are counted by the
graph homomorphisms. -/
theorem _root_.SimpleGraph.homCount_toUniformHypergraph :
    F.toUniformHypergraph.homCount G.toUniformHypergraph = Nat.card (F →g G) := by
  rw [SimpleGraph.card_hom_eq_card_adjPreservingMaps, Nat.card_eq_fintype_card,
    Fintype.card_subtype, homCount_def]
  simp_rw [SimpleGraph.isHom_toUniformHypergraph_iff]

/-- The injective homomorphisms between the `2`-uniform hypergraphs of two simple graphs are
counted by Mathlib's labelled copy count. -/
theorem _root_.SimpleGraph.injHomCount_toUniformHypergraph :
    F.toUniformHypergraph.injHomCount G.toUniformHypergraph = G.labelledCopyCount F := by
  rw [← SimpleGraph.card_injective_hom_eq_labelledCopyCount, injHomCount_def,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun f ↦ ⟨⟨f.1, fun {a b} hab ↦ SimpleGraph.isHom_toUniformHypergraph_iff.1 f.2 a b
        hab⟩, f.1.injective⟩
      invFun := fun φ ↦ ⟨⟨φ.1, φ.2⟩, SimpleGraph.isHom_toUniformHypergraph_iff.2
        fun _ _ hab ↦ φ.1.map_rel hab⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The homomorphism density of the `2`-uniform hypergraphs of two simple graphs is the graph
homomorphism density `TauCeti.DenseGraphLimits.homDensityFin`. -/
theorem _root_.SimpleGraph.homDensity_toUniformHypergraph :
    (F.toUniformHypergraph.homDensity G.toUniformHypergraph : ℝ) =
      DenseGraphLimits.homDensityFin F G := by
  rw [homDensity_def, DenseGraphLimits.homDensityFin_def,
    SimpleGraph.homCount_toUniformHypergraph]
  simp

/-- The injective homomorphism density of the `2`-uniform hypergraphs of two simple graphs is the
injective graph homomorphism density `TauCeti.DenseGraphLimits.injHomDensity`. -/
theorem _root_.SimpleGraph.injHomDensity_toUniformHypergraph :
    (F.toUniformHypergraph.injHomDensity G.toUniformHypergraph : ℝ) =
      DenseGraphLimits.injHomDensity F G := by
  rw [injHomDensity_def, DenseGraphLimits.injHomDensity_eq_labelledCopyCount_div,
    SimpleGraph.injHomCount_toUniformHypergraph]
  simp

end SimpleGraph

end TauCeti
