/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.Combinatorics.SimpleGraph.Density
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.PairCutCapacity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Lattice

/-!
# The edge boundary and the isoperimetric constant of a finite simple graph

For a finite simple graph `G` and a vertex set `S`, the edge boundary `G.edgeBoundary S` is the
finset `G.interedges S Sᶜ` of ordered adjacent pairs `(x, y)` with `x ∈ S` and `y ∉ S`; it is in
bijection with the edges leaving `S`. (It is the finite, ordered-pair counterpart for simple
graphs of the edge set `Graph.edgeCut` of Mathlib's multigraphs.) The isoperimetric constant (or
edge expansion) is `h(G) = min |∂S| / |S|`, the minimum over the nonempty vertex sets `S` with
`2|S| ≤ n`, where `n` is the number of vertices. A family of sparse graphs
whose isoperimetric constants are bounded away from `0` is a family of expanders.

## Main definitions

* `SimpleGraph.edgeBoundary G S`: the edge boundary `∂S`.
* `SimpleGraph.isoperimetricConstant G`: the isoperimetric constant `h(G)`. It is a real infimum
  over a finite index set, which is empty when `n ≤ 1`; the value is then `0`.

## Main results

* `SimpleGraph.card_edgeBoundary_compl`: `|∂Sᶜ| = |∂S|`.
* `SimpleGraph.card_edgeBoundary_eq_unitCutCapacity`: `|∂S|` is the number
  `SimpleGraph.unitCutCapacity G S` of edges of `G` crossing the cut `(S, Sᶜ)`.
* `SimpleGraph.sum_degree_eq_card_interedges_add_card_edgeBoundary`: the degrees in `S` add up
  to the ordered adjacent pairs inside `S` plus `|∂S|`; the former number is even
  (`SimpleGraph.even_card_interedges_self`). Hence in a preconnected graph every nonempty proper
  set whose vertices have even degrees has at least two boundary edges
  (`SimpleGraph.Preconnected.two_le_card_edgeBoundary_of_even_degree`).
* `SimpleGraph.exists_isoperimetricConstant_eq` and `SimpleGraph.isoperimetricConstant_le`: for
  `n ≥ 2` the infimum is attained and bounds every admissible set.
* `SimpleGraph.isoperimetricConstant_pos_iff_connected`: for `n ≥ 2`, `h(G) > 0` exactly when `G`
  is connected.
* `SimpleGraph.isoperimetricConstant_le_minDegree`: `h(G) ≤ δ(G)`.
* `SimpleGraph.isoperimetricConstant_mono`: adding edges does not decrease `h`.
* `SimpleGraph.isoperimetricConstant_top`: `h(Kₙ) = ⌈n/2⌉` for `n ≥ 2`.
* `SimpleGraph.isoperimetricConstant_cycleGraph`: `h(Cₙ) = 2/⌊n/2⌋` for `n ≥ 3`.

## References

* G. Davidoff, P. Sarnak and A. Valette, *Elementary Number Theory, Group Theory and Ramanujan
  Graphs*, London Math. Soc. Student Texts 55, Cambridge University Press (2003),
  Definition 1.2.1.
* B. Nica, *A Brief Introduction to Spectral Graph Theory*, EMS Textbooks in Mathematics (2018),
  §2.3.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### The edge boundary -/

/-- The edge boundary `∂S` of a vertex set `S`: the ordered adjacent pairs `(x, y)` with `x ∈ S`
and `y ∉ S`. It is in bijection with the edges of `G` leaving `S`. -/
def edgeBoundary (S : Finset V) : Finset (V × V) :=
  G.interedges S Sᶜ

theorem edgeBoundary_def (S : Finset V) : G.edgeBoundary S = G.interedges S Sᶜ := (rfl)

variable {G} in
@[simp]
theorem mem_edgeBoundary {S : Finset V} {x : V × V} :
    x ∈ G.edgeBoundary S ↔ x.1 ∈ S ∧ x.2 ∉ S ∧ G.Adj x.1 x.2 := by
  rw [edgeBoundary_def, mem_interedges_iff, mem_compl]

variable {G} in
theorem mk_mem_edgeBoundary {S : Finset V} {a b : V} :
    (a, b) ∈ G.edgeBoundary S ↔ a ∈ S ∧ b ∉ S ∧ G.Adj a b :=
  mem_edgeBoundary

@[simp]
theorem edgeBoundary_empty : G.edgeBoundary ∅ = ∅ := by
  ext; simp

@[simp]
theorem edgeBoundary_univ : G.edgeBoundary univ = ∅ := by
  ext; simp

/-- The edge boundary of a set and of its complement have the same size: swapping the two
coordinates exchanges them. -/
@[simp]
theorem card_edgeBoundary_compl (S : Finset V) :
    #(G.edgeBoundary Sᶜ) = #(G.edgeBoundary S) := by
  have := G.symm
  rw [edgeBoundary_def, edgeBoundary_def, compl_compl]
  exact Rel.card_interedges_comm _ _

/-- Adding edges enlarges every edge boundary. -/
theorem edgeBoundary_mono {H : SimpleGraph V} [DecidableRel H.Adj] (h : G ≤ H) (S : Finset V) :
    G.edgeBoundary S ⊆ H.edgeBoundary S := fun x hx ↦ by
  rw [mem_edgeBoundary] at hx ⊢
  exact ⟨hx.1, hx.2.1, h hx.2.2⟩

/-- The edge boundary of a single vertex consists of the pairs `(v, w)` with `w` a neighbour
of `v`. -/
theorem edgeBoundary_singleton (v : V) :
    G.edgeBoundary {v} = (G.neighborFinset v).map ⟨Prod.mk v, Prod.mk_right_injective v⟩ := by
  ext ⟨a, b⟩
  simp only [mk_mem_edgeBoundary, mem_singleton, mem_map, mem_neighborFinset,
    Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, -, hab⟩
    exact ⟨b, hab, rfl, rfl⟩
  · rintro ⟨c, hc, rfl, rfl⟩
    exact ⟨rfl, hc.ne', hc⟩

@[simp]
theorem card_edgeBoundary_singleton (v : V) : #(G.edgeBoundary {v}) = G.degree v := by
  rw [edgeBoundary_singleton, card_map, card_neighborFinset_eq_degree]

/-- The size of the edge boundary of `S` is the unit cut capacity of `S`: the number of edges
of `G` crossing the cut. -/
theorem card_edgeBoundary_eq_unitCutCapacity (S : Finset V) :
    #(G.edgeBoundary S) = G.unitCutCapacity S := by
  rw [unitCutCapacity_eq_ncard, ← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun p _ ↦ s(p.1, p.2)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    rw [mem_coe, mk_mem_edgeBoundary] at h
    exact ⟨h.2.2, Sym2.crosses_mk_iff.2 (.inl ⟨mod_cast h.1, mod_cast h.2.1⟩)⟩
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h h' he
    rw [mem_coe, mk_mem_edgeBoundary] at h h'
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd h.1 h'.2.1
  · intro e ⟨heG, heS⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [Set.mem_ofPred_eq, Sym2.crosses_mk_iff] at heS
      rcases heS with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact ⟨(a, b), mk_mem_edgeBoundary.2 ⟨mod_cast ha, mod_cast hb, heG⟩, rfl⟩
      · exact ⟨(b, a), mk_mem_edgeBoundary.2 ⟨mod_cast hb, mod_cast ha, heG.symm⟩,
          Sym2.eq_swap⟩

variable {G} in
/-- If `u ∈ S` can reach `v ∉ S`, then the edge boundary of `S` is nonempty. -/
theorem Reachable.edgeBoundary_nonempty {S : Finset V} {u v : V} (h : G.Reachable u v)
    (hu : u ∈ S) (hv : v ∉ S) : (G.edgeBoundary S).Nonempty := by
  obtain ⟨p⟩ := h
  obtain ⟨d, -, hd₁, hd₂⟩ := p.exists_boundary_dart (S : Set V) (mod_cast hu) (mod_cast hv)
  exact ⟨(d.fst, d.snd), mk_mem_edgeBoundary.2 ⟨mod_cast hd₁, mod_cast hd₂, d.adj⟩⟩

variable {G} in
/-- In a preconnected graph every nonempty proper vertex set has a nonempty edge boundary. -/
theorem Preconnected.edgeBoundary_nonempty (hG : G.Preconnected) {S : Finset V}
    (hS : S.Nonempty) (hS' : S ≠ univ) : (G.edgeBoundary S).Nonempty := by
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, -, hv⟩ := exists_of_ssubset (ssubset_univ_iff.2 hS')
  exact (hG u v).edgeBoundary_nonempty hu hv

/-- The degrees of the vertices of `S` add up to the number of ordered adjacent pairs inside `S`
plus the size of the edge boundary of `S`. -/
theorem sum_degree_eq_card_interedges_add_card_edgeBoundary (S : Finset V) :
    ∑ x ∈ S, G.degree x = #(G.interedges S S) + #(G.edgeBoundary S) := by
  rw [edgeBoundary_def, card_interedges_eq_sum, card_interedges_eq_sum, ← sum_add_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [← card_union_of_disjoint (disjoint_filter_filter disjoint_compl_right), ← filter_union,
    union_compl, ← neighborFinset_eq_filter, card_neighborFinset_eq_degree]

variable {G} in
/-- In a `k`-regular graph, `k |S|` is the number of ordered adjacent pairs inside `S` plus the
size of the edge boundary of `S`. -/
theorem IsRegularOfDegree.mul_card_eq_card_interedges_add_card_edgeBoundary {k : ℕ}
    (hG : G.IsRegularOfDegree k) (S : Finset V) :
    k * #S = #(G.interedges S S) + #(G.edgeBoundary S) := by
  rw [← sum_degree_eq_card_interedges_add_card_edgeBoundary, sum_congr rfl fun x _ ↦ hG x,
    sum_const, smul_eq_mul, mul_comm]

variable {G} in
/-- In a preconnected graph, every nonempty proper vertex set `S` whose vertices all have even
degree has at least two boundary edges: the boundary is nonempty by preconnectedness, and of even
size because the degrees in `S` add up to an even number. -/
theorem Preconnected.two_le_card_edgeBoundary_of_even_degree (hG : G.Preconnected) {S : Finset V}
    (hdeg : ∀ v ∈ S, Even (G.degree v)) (hS : S.Nonempty) (hS' : S ≠ univ) :
    2 ≤ #(G.edgeBoundary S) := by
  have hsum := G.sum_degree_eq_card_interedges_add_card_edgeBoundary S
  have hev : Even (∑ x ∈ S, G.degree x) := Finset.even_sum _ hdeg
  obtain ⟨r, hr⟩ := hev
  obtain ⟨t, ht⟩ := G.even_card_interedges_self S
  have hpos := (hG.edgeBoundary_nonempty hS hS').card_pos
  omega

/-! ### The isoperimetric constant -/

/-- The isoperimetric constant `h(G)`: the infimum of `|∂S| / |S|` over the nonempty vertex sets
`S` with `2|S| ≤ n`. The index set is finite, and empty when `n ≤ 1`, where the value is `0`. -/
noncomputable def isoperimetricConstant : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V},
    (#(G.edgeBoundary S.val) : ℝ) / #S.val

theorem isoperimetricConstant_def :
    G.isoperimetricConstant = ⨅ S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V},
      (#(G.edgeBoundary S.val) : ℝ) / #S.val := (rfl)

theorem isoperimetricConstant_nonneg : 0 ≤ G.isoperimetricConstant :=
  Real.iInf_nonneg fun _ ↦ by positivity

omit [DecidableEq V] in
/-- On at least two vertices some vertex set is admissible, for instance a single vertex. -/
private theorem nonempty_admissible (hV : 2 ≤ Fintype.card V) :
    Nonempty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 (by omega : 0 < Fintype.card V)
  exact ⟨⟨{v}, singleton_nonempty v, by simpa using hV⟩⟩

/-- The isoperimetric constant bounds `|∂S| / |S|` for every admissible set `S`. -/
theorem isoperimetricConstant_le {S : Finset V} (hS : S.Nonempty)
    (hS' : 2 * #S ≤ Fintype.card V) :
    G.isoperimetricConstant ≤ #(G.edgeBoundary S) / #S :=
  Finite.ciInf_le_of_le ⟨S, hS, hS'⟩ le_rfl

/-- On at least two vertices, a lower bound for `|∂S| / |S|` on every admissible set `S` is a
lower bound for the isoperimetric constant. -/
theorem le_isoperimetricConstant (hV : 2 ≤ Fintype.card V) {c : ℝ}
    (h : ∀ S : Finset V, S.Nonempty → 2 * #S ≤ Fintype.card V → c ≤ #(G.edgeBoundary S) / #S) :
    c ≤ G.isoperimetricConstant := by
  have := nonempty_admissible (V := V) hV
  exact le_ciInf fun S ↦ h S.val S.property.1 S.property.2

/-- On at least two vertices the isoperimetric constant is attained by an admissible set. -/
theorem exists_isoperimetricConstant_eq (hV : 2 ≤ Fintype.card V) :
    ∃ S : Finset V, S.Nonempty ∧ 2 * #S ≤ Fintype.card V ∧
      G.isoperimetricConstant = #(G.edgeBoundary S) / #S := by
  have := nonempty_admissible (V := V) hV
  obtain ⟨S, hS⟩ := Finite.exists_min
    fun S : {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} ↦
      (#(G.edgeBoundary S.val) : ℝ) / #S.val
  exact ⟨S.val, S.property.1, S.property.2,
    le_antisymm (G.isoperimetricConstant_le S.property.1 S.property.2) (le_ciInf hS)⟩

/-- On at most one vertex there is no admissible set, and the isoperimetric constant is `0`. -/
theorem isoperimetricConstant_of_card_lt_two (hV : Fintype.card V < 2) :
    G.isoperimetricConstant = 0 := by
  have : IsEmpty {S : Finset V // S.Nonempty ∧ 2 * #S ≤ Fintype.card V} :=
    ⟨fun S ↦ by have := S.property.1.card_pos; omega⟩
  exact Real.iInf_of_isEmpty _

/-- A disconnected graph has isoperimetric constant `0`: a connected component, or its
complement, is an admissible set with empty edge boundary. -/
theorem isoperimetricConstant_eq_zero_of_not_connected (hG : ¬G.Connected) :
    G.isoperimetricConstant = 0 := by
  classical
  rcases lt_or_ge (Fintype.card V) 2 with hV | hV
  · exact G.isoperimetricConstant_of_card_lt_two hV
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hpre : ¬G.Preconnected := fun h ↦ hG ⟨h⟩
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬G.Reachable u v := by
    simpa [Preconnected] using hpre
  let S : Finset V := {w | G.Reachable u w}
  have hu : u ∈ S := by simp [S]
  have hv : v ∉ S := by simpa [S] using huv
  have hbd : G.edgeBoundary S = ∅ := by
    refine eq_empty_of_forall_notMem fun ⟨a, b⟩ h ↦ ?_
    simp only [mk_mem_edgeBoundary, S, mem_filter, mem_univ, true_and] at h
    exact h.2.1 (h.1.trans h.2.2.reachable)
  have hbdc : G.edgeBoundary Sᶜ = ∅ := by
    rw [← card_eq_zero, card_edgeBoundary_compl, hbd, card_empty]
  refine le_antisymm ?_ G.isoperimetricConstant_nonneg
  rcases le_total (2 * #S) (Fintype.card V) with hS | hS
  · simpa [hbd] using G.isoperimetricConstant_le ⟨u, hu⟩ hS
  · have hSc : 2 * #Sᶜ ≤ Fintype.card V := by
      rw [card_compl]
      have := card_le_univ S
      omega
    simpa [hbdc] using G.isoperimetricConstant_le ⟨v, mem_compl.2 hv⟩ hSc

/-- On at least two vertices the isoperimetric constant is positive exactly when the graph is
connected. -/
theorem isoperimetricConstant_pos_iff_connected (hV : 2 ≤ Fintype.card V) :
    0 < G.isoperimetricConstant ↔ G.Connected := by
  refine ⟨fun h ↦ by_contra fun hG ↦ h.ne' (G.isoperimetricConstant_eq_zero_of_not_connected hG),
    fun hG ↦ ?_⟩
  obtain ⟨S, hS, hS', heq⟩ := G.exists_isoperimetricConstant_eq hV
  rw [heq]
  have := hS.card_pos
  have := (hG.preconnected.edgeBoundary_nonempty hS
    ((card_lt_iff_ne_univ S).1 (by omega))).card_pos
  positivity

/-- The isoperimetric constant is at most the degree of any vertex: on at least two vertices take
`S` to be that vertex; on one vertex the constant is `0`. -/
theorem isoperimetricConstant_le_degree (v : V) : G.isoperimetricConstant ≤ G.degree v := by
  rcases lt_or_ge (Fintype.card V) 2 with hV | hV
  · rw [G.isoperimetricConstant_of_card_lt_two hV]
    exact Nat.cast_nonneg _
  · simpa using G.isoperimetricConstant_le (singleton_nonempty v) (by simpa using hV)

/-- The isoperimetric constant is at most the minimum degree. -/
theorem isoperimetricConstant_le_minDegree : G.isoperimetricConstant ≤ G.minDegree := by
  cases isEmpty_or_nonempty V
  · rw [G.isoperimetricConstant_of_card_lt_two (by simp), minDegree_of_subsingleton, Nat.cast_zero]
  · obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
    rw [hv]
    exact G.isoperimetricConstant_le_degree v

/-- Adding edges does not decrease the isoperimetric constant. -/
theorem isoperimetricConstant_mono {H : SimpleGraph V} [DecidableRel H.Adj] (h : G ≤ H) :
    G.isoperimetricConstant ≤ H.isoperimetricConstant :=
  Finite.ciInf_mono fun S ↦ div_le_div_of_nonneg_right
    (mod_cast card_le_card (G.edgeBoundary_mono h S.val)) (Nat.cast_nonneg _)

/-! ### Complete graphs and cycles -/

/-- In the complete graph the edge boundary of `S` is all of `S ×ˢ Sᶜ`. -/
theorem edgeBoundary_top (S : Finset V) : (⊤ : SimpleGraph V).edgeBoundary S = S ×ˢ Sᶜ := by
  ext ⟨a, b⟩
  simp only [mk_mem_edgeBoundary, top_adj, mem_product, mem_compl]
  constructor
  · rintro ⟨ha, hb, -⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha, hb, fun h ↦ hb (h ▸ ha)⟩

/-- The complete graph on `n ≥ 2` vertices has isoperimetric constant `⌈n/2⌉ = (n + 1) / 2`: a
set `S` has `|∂S| / |S| = n - |S|`, least when `|S| = ⌊n/2⌋`. -/
theorem isoperimetricConstant_top (hV : 2 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).isoperimetricConstant = ((Fintype.card V + 1) / 2 : ℕ) := by
  have hratio : ∀ S : Finset V, S.Nonempty →
      (#((⊤ : SimpleGraph V).edgeBoundary S) : ℝ) / #S = (Fintype.card V - #S : ℕ) := by
    intro S hS
    have := hS.card_pos
    rw [edgeBoundary_top, card_product, card_compl, Nat.cast_mul,
      mul_div_cancel_left₀ _ (by positivity)]
  refine le_antisymm ?_ ((⊤ : SimpleGraph V).le_isoperimetricConstant hV fun S hS hS' ↦ ?_)
  · obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset V))
      (n := Fintype.card V / 2) (by rw [card_univ]; omega)
    have hne : S.Nonempty := card_pos.1 (by omega)
    calc (⊤ : SimpleGraph V).isoperimetricConstant
        ≤ #((⊤ : SimpleGraph V).edgeBoundary S) / #S :=
          (⊤ : SimpleGraph V).isoperimetricConstant_le hne (by omega)
      _ = ((Fintype.card V + 1) / 2 : ℕ) := by
          rw [hratio S hne, hS]
          congr 1
          omega
  · rw [hratio S hS]
    exact_mod_cast (by omega : (Fintype.card V + 1) / 2 ≤ Fintype.card V - #S)

/-- The cycle `Cₙ` on `n ≥ 3` vertices has isoperimetric constant `2/⌊n/2⌋`: every admissible
set has at least two boundary edges (the cycle is connected and `2`-regular) and at most `⌊n/2⌋`
vertices, and an arc of `⌊n/2⌋`
consecutive vertices has exactly two boundary edges. -/
theorem isoperimetricConstant_cycleGraph {n : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).isoperimetricConstant = 2 / (n / 2 : ℕ) := by
  have hV : 2 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  have hm : 0 < n / 2 := by omega
  refine le_antisymm ?_ ((cycleGraph n).le_isoperimetricConstant hV fun S hS hS' ↦ ?_)
  · -- The arc `{0, …, ⌊n/2⌋ - 1}` has boundary contained in `{(⌊n/2⌋ - 1, ⌊n/2⌋), (0, n - 1)}`.
    let S : Finset (Fin n) := {i | (i : ℕ) < n / 2}
    have hcard : #S = n / 2 := by
      rw [Fin.card_filter_val_lt]; omega
    have hne : S.Nonempty := card_pos.1 (by omega)
    have hsub : (cycleGraph n).edgeBoundary S ⊆
        {(⟨n / 2 - 1, by omega⟩, ⟨n / 2, by omega⟩), (⟨0, by omega⟩, ⟨n - 1, by omega⟩)} := by
      rintro ⟨a, b⟩ h
      simp only [mk_mem_edgeBoundary, S, mem_filter, mem_univ, true_and, not_lt,
        cycleGraph_adj'] at h
      obtain ⟨ha, hb, hab | hab⟩ := h
      · rw [Fin.coe_sub_iff_lt.2 (Fin.lt_def.2 (by omega))] at hab
        have := b.isLt
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, Fin.ext_iff]
        omega
      · rw [Fin.coe_sub_iff_le.2 (Fin.le_def.2 (by omega))] at hab
        simp only [mem_insert, mem_singleton, Prod.mk.injEq, Fin.ext_iff]
        omega
    have hle : #((cycleGraph n).edgeBoundary S) ≤ 2 := (card_le_card hsub).trans card_le_two
    calc (cycleGraph n).isoperimetricConstant
        ≤ #((cycleGraph n).edgeBoundary S) / #S :=
          (cycleGraph n).isoperimetricConstant_le hne (by rw [hcard, Fintype.card_fin]; omega)
      _ ≤ 2 / (n / 2 : ℕ) := by
          rw [hcard]
          gcongr
          exact_mod_cast hle
  · have := hS.card_pos
    have hne := (card_lt_iff_ne_univ S).1 (by omega)
    have hconn : (cycleGraph n).Connected := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact connected_cycleGraph_add_one
    have h2 := hconn.preconnected.two_le_card_edgeBoundary_of_even_degree (fun v _ ↦ by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      rw [cycleGraph_degree_three_le]
      exact even_two) hS hne
    have hSm : #S ≤ n / 2 := by rw [Fintype.card_fin] at hS'; omega
    calc (2 : ℝ) / (n / 2 : ℕ) ≤ 2 / #S := by gcongr
      _ ≤ #((cycleGraph n).edgeBoundary S) / #S := by gcongr; exact_mod_cast h2

/-! ### Summary -/

/-- The basic properties of the isoperimetric constant on at least two vertices: it is attained
by an admissible set and bounds every admissible set; the edge boundaries of a set and of its
complement have the same size; and `h(G) > 0` exactly when `G` is connected. -/
theorem isoperimetricConstant_spec (hV : 2 ≤ Fintype.card V) :
    (∃ S : Finset V, S.Nonempty ∧ 2 * #S ≤ Fintype.card V ∧
      G.isoperimetricConstant = #(G.edgeBoundary S) / #S) ∧
    (∀ S : Finset V, S.Nonempty → 2 * #S ≤ Fintype.card V →
      G.isoperimetricConstant ≤ #(G.edgeBoundary S) / #S) ∧
    (∀ S : Finset V, #(G.edgeBoundary Sᶜ) = #(G.edgeBoundary S)) ∧
    (0 < G.isoperimetricConstant ↔ G.Connected) :=
  ⟨G.exists_isoperimetricConstant_eq hV, fun _ ↦ G.isoperimetricConstant_le,
    G.card_edgeBoundary_compl, G.isoperimetricConstant_pos_iff_connected hV⟩

end SimpleGraph
