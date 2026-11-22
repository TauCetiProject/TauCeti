/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Invariance
public import TauCeti.Combinatorics.SimpleGraph.EdgeLabel
public import TauCeti.Combinatorics.SimpleGraph.OddTriple.Basic
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Graph cochains and support graphs

Every `1`-cochain `α : TauCeti.Cochain X Γ` has a support graph `α.supportGraph` whose edges are
the vertex pairs where `α u v ≠ 1`. Conversely, a simple graph `G` on a finite vertex type `V` and
an involution `c : Γ` (`c * c = 1`) define a `1`-cochain `G.toCochain hc` on
`TauCeti.TwoComplex.complete V` assigning `c` to adjacent pairs and `1` to non-adjacent pairs.

## Main definitions and results

* `TauCeti.Cochain.supportGraph`, `TauCeti.Cochain.supportGraph_one`,
  `TauCeti.Cochain.supportGraph_comapComplete`, `TauCeti.Cochain.supportGraph_map`: the simple
  graph of vertex pairs where `α u v ≠ 1`, its normal form on `1`, and its compatibility with
  vertex pullback and injective coefficient maps.
* `SimpleGraph.toCochain`: the `{1, c}`-valued `1`-cochain on `TwoComplex.complete V` supported
  on `G` for an element `c * c = 1`.
* `SimpleGraph.smul_ite_mem_toCochain`, `SimpleGraph.cost_toCochain_ite_mem`: acting by the
  `{1, c}`-indicator gauge of `S` switches `G` to `G ∆ (⊤ : SimpleGraph V).between S Sᶜ` and
  costs `#(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset * ℓ c`.
* `SimpleGraph.holonomy_toCochain`, `SimpleGraph.defect_toCochain`: holonomy around `(u, v, w)`
  tracks edge-parity around `(u, v, w)`, and defect equals `#G.oddTripleFinset * ℓ c`.
* `SimpleGraph.isCoboundary_toCochain_iff`: for nontrivial `c` (`c * c = 1`, `c ≠ 1`),
  `G.toCochain hc` is a coboundary iff `G` is a complete-graph cut.
* `TauCeti.Cochain.exists_map_zpowers_subtype_eq_toCochain`: every `Subgroup.zpowers c`-valued
  `1`-cochain on `TwoComplex.complete V` embeds as `G.toCochain hc`.
-/

public section

open Finset
open scoped symmDiff

namespace TauCeti

namespace Cochain

/-- The simple graph underlying a `1`-cochain `α : Cochain X Γ`: two vertices are adjacent
precisely when `α u v ≠ 1`. -/
def supportGraph {V Γ : Type*} [Group Γ] {X : TwoComplex V} (α : Cochain X Γ) :
    SimpleGraph V where
  Adj u v := α u v ≠ 1
  symm := ⟨by intro u v h; rwa [α.apply_swap, inv_ne_one]⟩
  loopless := ⟨by intro u h; exact h (α.apply_self u)⟩

/-- Two vertices are adjacent in `α.supportGraph` precisely when `α u v ≠ 1`. -/
@[simp, grind =]
theorem supportGraph_adj {V Γ : Type*} [Group Γ] {X : TwoComplex V}
    (α : Cochain X Γ) (u v : V) :
    α.supportGraph.Adj u v ↔ α u v ≠ 1 :=
  Iff.rfl

/-- The trivial `1`-cochain has the empty support graph. -/
@[simp]
theorem supportGraph_one {V Γ : Type*} [Group Γ] {X : TwoComplex V} :
    (1 : Cochain X Γ).supportGraph = ⊥ := by
  ext u v
  simp

instance instDecidableRelSupportGraphAdj {V Γ : Type*} [Group Γ] [DecidableEq Γ]
    {X : TwoComplex V} (α : Cochain X Γ) :
    DecidableRel α.supportGraph.Adj :=
  fun u v ↦ inferInstanceAs (Decidable (α u v ≠ 1))

/-- Pulling a cochain on `TwoComplex.complete V` back along `f : W → V` pulls its support graph
back along `f`. -/
@[simp]
theorem supportGraph_comapComplete {V W Γ : Type*} [Fintype V] [Fintype W] [Group Γ]
    (α : Cochain (TwoComplex.complete V) Γ) (f : W → V) :
    (α.comapComplete f).supportGraph = α.supportGraph.comap f := by
  ext u v
  simp

/-- Pushing a cochain forward along an injective group homomorphism preserves its support graph. -/
@[simp]
theorem supportGraph_map {V Γ H : Type*} [Group Γ] [Group H] {X : TwoComplex V}
    (α : Cochain X Γ) {φ : Γ →* H} (hφ : Function.Injective φ) :
    (α.map φ).supportGraph = α.supportGraph := by
  ext u v
  simp [map_eq_one_iff φ hφ]

end Cochain

end TauCeti

namespace SimpleGraph

section Involution

variable {V Γ : Type*}

/-- The `Γ`-valued `1`-cochain on `TwoComplex.complete V` associated to a simple graph `G` and an
element `c : Γ` satisfying `c * c = 1`, assigning `c` to adjacent vertex pairs and `1` to
non-adjacent pairs. -/
noncomputable def toCochain [Fintype V] [Group Γ] (G : SimpleGraph V) {c : Γ} (hc : c * c = 1) :
    TauCeti.Cochain (TauCeti.TwoComplex.complete V) Γ :=
  open Classical in
  TauCeti.Cochain.ofFn (TauCeti.TwoComplex.complete V)
    (fun u v ↦ if G.Adj u v then c else 1)
    fun u v _ ↦ G.ite_adj_eq_inv_of_mul_self_eq_one hc u v

/-- `G.toCochain hc` takes the value `c` on adjacent vertices. -/
@[simp, grind =]
theorem toCochain_apply_of_adj [Fintype V] [Group Γ] {G : SimpleGraph V} {c : Γ}
    (hc : c * c = 1) {u v : V} (h : G.Adj u v) :
    G.toCochain hc u v = c := by
  simp [toCochain, (TauCeti.TwoComplex.adj_complete u v).mpr h.ne, h]

/-- `G.toCochain hc` takes the value `1` on non-adjacent vertices. -/
@[simp, grind =]
theorem toCochain_apply_of_not_adj [Fintype V] [Group Γ] {G : SimpleGraph V} {c : Γ}
    (hc : c * c = 1) {u v : V} (h : ¬ G.Adj u v) :
    G.toCochain hc u v = 1 := by
  rcases eq_or_ne u v with rfl | huv
  · exact (G.toCochain hc).apply_self u
  · simp [toCochain, (TauCeti.TwoComplex.adj_complete u v).mpr huv, h]

/-- Explicit `ite` evaluation of `G.toCochain hc` when adjacency in `G` is decidable. -/
theorem toCochain_apply [Fintype V] [Group Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v : V) :
    G.toCochain hc u v = if G.Adj u v then c else 1 := by
  by_cases h : G.Adj u v <;> simp [h]

/-- For nontrivial `c` (`c * c = 1`, `c ≠ 1`), `G.toCochain hc u v ≠ 1` iff `G.Adj u v`. -/
@[simp]
theorem toCochain_ne_one_iff [Fintype V] [Group Γ] (G : SimpleGraph V) {c : Γ}
    (hc : c * c = 1) (hc₁ : c ≠ 1) (u v : V) :
    G.toCochain hc u v ≠ 1 ↔ G.Adj u v := by
  classical
  rw [G.toCochain_apply hc]
  split_ifs with h <;> simp [h, hc₁]

/-- For nontrivial `c` (`c * c = 1`, `c ≠ 1`), the support graph of `G.toCochain hc` is `G`. -/
@[simp]
theorem supportGraph_toCochain [Fintype V] [Group Γ] (G : SimpleGraph V) {c : Γ}
    (hc : c * c = 1) (hc₁ : c ≠ 1) :
    (G.toCochain hc).supportGraph = G := by
  ext u v
  simp [hc₁]

/-- The empty graph induces the trivial `1`-cochain. -/
@[simp]
theorem bot_toCochain [Fintype V] [Group Γ] {c : Γ} (hc : c * c = 1) :
    (⊥ : SimpleGraph V).toCochain hc = 1 := by
  ext u v _
  simp

/-- A single-edge graph `SimpleGraph.edge u v` induces `Cochain.singleEdge` on
`TwoComplex.complete V`. -/
theorem edge_toCochain [Fintype V] [Group Γ] (u v : V) {c : Γ} (hc : c * c = 1) :
    (edge u v).toCochain hc =
      TauCeti.Cochain.singleEdge (TauCeti.TwoComplex.complete V) u v c := by
  rcases eq_or_ne u v with rfl | huv
  · have he : edge u u = ⊥ := by
      ext x y
      simp
    rw [he, bot_toCochain hc,
      TauCeti.Cochain.singleEdge_of_not_adj ((TauCeti.TwoComplex.complete V).not_adj_self u)]
  · ext x y _
    by_cases h₁ : x = u ∧ y = v
    · obtain ⟨hx, hy⟩ := h₁
      rw [hx, hy, toCochain_apply_of_adj hc ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩),
        TauCeti.Cochain.singleEdge_apply_self ((TauCeti.TwoComplex.adj_complete u v).mpr huv)]
    · by_cases h₂ : x = v ∧ y = u
      · obtain ⟨hx, hy⟩ := h₂
        rw [hx, hy, toCochain_apply_of_adj hc ((edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩),
          TauCeti.Cochain.singleEdge_apply_swap ((TauCeti.TwoComplex.adj_complete u v).mpr huv),
          inv_eq_of_mul_eq_one_right hc]
      · have hnadj : ¬ (edge u v).Adj x y := by
          rw [edge_adj]
          rintro ⟨h | h, -⟩
          · exact h₁ h
          · exact h₂ h
        rw [toCochain_apply_of_not_adj hc hnadj, TauCeti.Cochain.singleEdge_apply_of_ne c h₁ h₂]

/-- Pushing `G.toCochain hc` forward along a group homomorphism `φ` yields `G.toCochain` for
`φ c`. -/
@[simp]
theorem map_toCochain {H : Type*} [Fintype V] [Group Γ] [Group H] (G : SimpleGraph V)
    {c : Γ} (hc : c * c = 1) (φ : Γ →* H) :
    (G.toCochain hc).map φ = G.toCochain (by rw [← map_mul, hc, map_one] : φ c * φ c = 1) := by
  ext u v _
  by_cases h : G.Adj u v <;> simp [h]

/-- Acting on `G.toCochain hc` by the `{1, c}`-valued indicator gauge of `S` switches `G` by the
complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ`. -/
theorem smul_ite_mem_toCochain [Fintype V] [Group Γ] (G : SimpleGraph V)
    {c : Γ} (hc : c * c = 1) (S : Set V) [DecidablePred (· ∈ S)] :
    (fun v ↦ if v ∈ S then c else 1) • G.toCochain hc =
      (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).toCochain hc := by
  classical
  ext u v _
  rw [TauCeti.Cochain.smul_apply_complete, G.toCochain_apply hc, (G ∆ _).toCochain_apply hc]
  exact G.ite_mem_inv_mul_ite_adj_mul hc S u v

/-- The holonomy of `G.toCochain hc` around `(u, v, w)` equals `c` if an odd number of the pairs
`(u, v)`, `(v, w)`, and `(w, u)` are adjacent in `G` (equivalently, if `{u, v, w}` spans an odd
number of edges when `u`, `v`, `w` are pairwise distinct), and `1` otherwise. -/
theorem holonomy_toCochain [Fintype V] [Group Γ] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : Γ} (hc : c * c = 1) (u v w : V) :
    (G.toCochain hc).holonomy u v w =
      if Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u)) then c else 1 := by
  simp only [TauCeti.Cochain.holonomy_def, G.toCochain_apply hc]
  exact G.ite_adj_mul_ite_adj_mul_ite_adj hc u v w

/-- Under the trivial gauge `1`, the cost of `G.toCochain hc` equals `#G.edgeFinset * ℓ c`. -/
theorem cost_toCochain_one [Fintype V] [LinearOrder V] [Group Γ] (G : SimpleGraph V)
    [Fintype G.edgeSet] (ℓ : GroupNorm Γ) {c : Γ} (hc : c * c = 1) :
    (G.toCochain hc).cost ℓ 1 = #G.edgeFinset * ℓ c := by
  classical
  rw [TauCeti.Cochain.cost_complete, G.card_edgeFinset_eq_card_filter_lt]
  simp_rw [Pi.one_apply, inv_one, one_mul, mul_one, G.toCochain_apply hc, apply_ite ℓ,
    map_one_eq_zero ℓ, ← sum_filter, filter_filter, sum_const, nsmul_eq_mul]

/-- Under the `{1, c}`-valued indicator gauge of `S`, the cost of `G.toCochain hc` equals
`#(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset * ℓ c`. -/
theorem cost_toCochain_ite_mem [Fintype V] [LinearOrder V] [Group Γ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ℓ : GroupNorm Γ) {c : Γ} (hc : c * c = 1)
    (S : Set V) [DecidablePred (· ∈ S)] :
    (G.toCochain hc).cost ℓ (fun v ↦ if v ∈ S then c else 1) =
      #(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).edgeFinset * ℓ c := by
  have hsmul := (G.toCochain hc).cost_smul ℓ (fun v ↦ if v ∈ S then c else 1) 1
  rw [mul_one, G.smul_ite_mem_toCochain hc S, (G ∆ _).cost_toCochain_one ℓ hc] at hsmul
  exact hsmul.symm

/-- The defect of `G.toCochain hc` equals `#G.oddTripleFinset * ℓ c`. -/
theorem defect_toCochain [Fintype V] [LinearOrder V] [Group Γ] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ℓ : GroupNorm Γ) {c : Γ} (hc : c * c = 1) :
    (G.toCochain hc).defect ℓ = #G.oddTripleFinset * ℓ c := by
  rw [TauCeti.Cochain.defect_complete, G.card_oddTripleFinset_eq_card_filter_lt]
  simp_rw [G.holonomy_toCochain hc, apply_ite ℓ, map_one_eq_zero ℓ, ← sum_filter, filter_filter,
    sum_const, nsmul_eq_mul, and_assoc]

/-- For any nontrivial involution `c : Γ` (`c * c = 1`, `c ≠ 1`), `G.toCochain hc` is a
coboundary on `TwoComplex.complete V` if and only if `G` is a complete-graph cut. -/
theorem isCoboundary_toCochain_iff [Fintype V] [Group Γ] (G : SimpleGraph V)
    {c : Γ} (hc : c * c = 1) (hc₁ : c ≠ 1) :
    (G.toCochain hc).IsCoboundary ↔
      ∃ S : Set V, G = (⊤ : SimpleGraph V).between S Sᶜ := by
  rw [TauCeti.Cochain.isCoboundary_complete]
  constructor
  · rintro ⟨β, hβ⟩
    rcases isEmpty_or_nonempty V with _ | ⟨⟨a⟩⟩
    · refine ⟨∅, ?_⟩
      ext u
      exact isEmptyElim u
    · classical
      refine ⟨{v | G.Adj a v}, ?_⟩
      have hinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
      have hγ (v : V) :
          β v * (β a)⁻¹ = if G.Adj a v then c else 1 := by
        have h := congrArg (·⁻¹) (hβ a v)
        rw [mul_inv_rev, inv_inv] at h
        rw [← h]
        by_cases hav : G.Adj a v <;> simp [hav, hinv]
      have hto (u v : V) :
          G.toCochain hc u v = (if G.Adj a u then c else 1) * (if G.Adj a v then c else 1)⁻¹ := by
        rw [← hγ u, ← hγ v, hβ u v]
        group
      ext u v
      rw [← G.toCochain_ne_one_iff hc hc₁ u v, hto u v, top_between_compl_adj,
        Set.mem_ofPred_eq, Set.mem_ofPred_eq]
      by_cases hu : G.Adj a u <;> by_cases hv : G.Adj a v <;>
        simp [hu, hv, hc, hinv, hc₁]
  · rintro ⟨S, rfl⟩
    classical
    refine ⟨fun v ↦ if v ∈ S then c else 1, fun u v ↦ ?_⟩
    simp only [SimpleGraph.toCochain_apply, top_between_compl_adj]
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
      simp [hu, hv, hc, inv_eq_of_mul_eq_one_right hc]

end Involution

end SimpleGraph

namespace TauCeti

namespace Cochain

/-- Every `Subgroup.zpowers c`-valued `1`-cochain on `TwoComplex.complete V` for an element
`c * c = 1` embeds into `Γ` as `G.toCochain hc` for some simple graph `G`. -/
theorem exists_map_zpowers_subtype_eq_toCochain {V Γ : Type*} [Fintype V] [Group Γ]
    {c : Γ} (hc : c * c = 1) (γ : Cochain (TwoComplex.complete V) (Subgroup.zpowers c)) :
    ∃ G : SimpleGraph V, γ.map (Subgroup.zpowers c).subtype = G.toCochain hc := by
  rcases eq_or_ne c 1 with rfl | hc1
  · refine ⟨⊥, ?_⟩
    ext u v _
    rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one (by simp)).mp (γ u v).property with h | h <;>
      simp [h]
  · refine ⟨γ.supportGraph, ?_⟩
    ext u v _
    rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one (sq c ▸ hc)).mp (γ u v).property with h | h
    · have h1 : γ u v = 1 := Subtype.ext h
      rw [map_apply, Subgroup.coe_subtype, h,
        SimpleGraph.toCochain_apply_of_not_adj hc (by simp [h1])]
    · have hadj : γ.supportGraph.Adj u v := fun h1 ↦
        hc1 (h.symm.trans (congrArg Subtype.val h1))
      rw [map_apply, Subgroup.coe_subtype, h, SimpleGraph.toCochain_apply_of_adj hc hadj]

end Cochain

end TauCeti
