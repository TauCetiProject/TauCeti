/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Bipartition
public import TauCeti.Combinatorics.Graph.Matching.Basic
public import TauCeti.Combinatorics.Network.Menger.SetToSet

/-!
# Multiset capacitated matchings and Kőnig's theorem

Let `G : Graph α β` be a multigraph with finitely many actual edges and let `b v : ℕ` be a capacity
on every actual vertex. A *multiset capacitated matching* assigns a multiplicity `x e : ℕ` to every
actual edge so that, at every actual vertex `v`, the edges incident with `v` have total multiplicity
at most `b v`; its *size* is `∑ e, x e`. An edge may be used repeatedly, whether or not the graph
has parallel edges, and a loop at `v` counts once towards the usage of `v`. A *vertex cover* is a
set of actual vertices meeting every edge, and the weight of a finite cover `C` is
`∑ v ∈ C, b v`. At `b = 1` a multiset capacitated matching uses every edge at most once and no two
edges with a common end, so it is an ordinary matching, and the weight of a cover is its size.

This file proves the multiset capacitated form of Kőnig's theorem for bipartite multigraphs: some
multiset capacitated matching has size equal to the weight of some vertex cover. Every multiset
capacitated matching has size at most the weight of every vertex cover, so this matching is then
largest and this cover of least weight. Weak duality holds in every multigraph, with loops; only
attainment needs the bipartition. Zero capacities, isolated vertices, empty sides and the empty
graph are all allowed.

## Main definitions

* `Graph.IsCapacitatedMatching G b x`: the edge multiplicities `x` form a multiset capacitated
  matching for the vertex capacities `b`.

## Main results

* `Graph.IsCapacitatedMatching.sum_le_sum_of_isVertexCover`: **weak duality**, the size of a
  multiset capacitated matching is at most the weight of any vertex cover.
* `Graph.IsBipartition.exists_isCapacitatedMatching_isVertexCover_sum_eq`: **Kőnig's theorem** for
  multiset capacitated matchings in bipartite multigraphs, in witness form.

## Implementation notes

Attainment is the vertex-capacitated set-to-set form of Menger's theorem
(`TauCeti.exists_paths_setSeparator_sum_eq`) for the arrow family on the actual vertices with one
arrow for every actual edge, from its end in `L` to its end in `R`, between the vertex sets `L` and
`R` and with the capacities `b`. Every member of a packing joins a vertex of `L` to a vertex of `R`,
so it traverses an arrow, and the edge of such an arrow has both ends among the vertices of the
member. Counting the members through each edge therefore gives a multiset capacitated matching of
size the number of members. A separator meets every one-arrow walk, so it is a vertex cover.

## References

* D. Kőnig, *Gráfok és mátrixok*, Mat. Fiz. Lapok 38 (1931).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 21.1.
-/

public section

open Finset TauCeti
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-! ### Multiset capacitated matchings -/

variable [Fintype E(G)] {b b' : V(G) → ℕ} {x y : E(G) → ℕ}

variable (G) in
/-- The edge multiplicities `x` form a *multiset capacitated matching* for the vertex capacities
`b`: at every actual vertex `v`, the actual edges incident with `v` have total multiplicity at most
`b v`. A loop at `v` counts once towards this total. -/
def IsCapacitatedMatching (b : V(G) → ℕ) (x : E(G) → ℕ) : Prop :=
  ∀ v, ∑ e ∈ G.incidentEdges {v}, x e ≤ b v

theorem isCapacitatedMatching_def :
    G.IsCapacitatedMatching b x ↔ ∀ v, ∑ e ∈ G.incidentEdges {v}, x e ≤ b v :=
  Iff.rfl

/-- Using no edge at all is a multiset capacitated matching. -/
@[simp]
theorem isCapacitatedMatching_zero : G.IsCapacitatedMatching b 0 :=
  fun _ ↦ by simp

/-! ### Ordinary matchings as unit-capacity matchings -/

/-- The unit multiplicity of a finite set of actual edges: selected edges have multiplicity one
and all other edges have multiplicity zero. -/
noncomputable def matchingMultiplicity (M : Finset E(G)) : E(G) → ℕ := by
  classical
  exact fun e ↦ if e ∈ M then 1 else 0

omit [Fintype E(G)] in
@[simp]
theorem matchingMultiplicity_eq_one_iff (M : Finset E(G)) (e : E(G)) :
    G.matchingMultiplicity M e = 1 ↔ e ∈ M := by
  classical
  simp [matchingMultiplicity]

omit [Fintype E(G)] in
theorem matchingMultiplicity_ne_zero_iff (M : Finset E(G)) (e : E(G)) :
    G.matchingMultiplicity M e ≠ 0 ↔ e ∈ M := by
  classical
  simp [matchingMultiplicity]

omit [Fintype E(G)] in
@[simp]
theorem matchingMultiplicity_eq_zero_iff (M : Finset E(G)) (e : E(G)) :
    G.matchingMultiplicity M e = 0 ↔ e ∉ M := by
  classical
  simp [matchingMultiplicity]

/-- In a loopless multigraph, ordinary matchings are exactly unit-capacity multiset matchings
whose multiplicities are the characteristic function of the selected edges. -/
theorem isMatching_iff_isCapacitatedMatching_matchingMultiplicity [G.Loopless]
    (M : Finset E(G)) :
    G.IsMatching M ↔ G.IsCapacitatedMatching 1 (G.matchingMultiplicity M) := by
  rw [isMatching_iff, isCapacitatedMatching_def]
  constructor
  · rintro ⟨_, huniq⟩ v
    rw [Pi.one_apply, Finset.sum_le_one_iff]
    intro e f he hf he0 hf0
    have heM := (matchingMultiplicity_ne_zero_iff M e).1 he0
    have hfM := (matchingMultiplicity_ne_zero_iff M f).1 hf0
    obtain ⟨w, hw, heInc⟩ := (Graph.mem_incidentEdges G).1 he
    obtain ⟨z, hz, hfInc⟩ := (Graph.mem_incidentEdges G).1 hf
    simp only [mem_singleton] at hw hz
    subst w
    subst z
    exact ⟨huniq v e heM heInc f hfM hfInc,
      (matchingMultiplicity_eq_one_iff M e).2 heM⟩
  · intro h
    refine ⟨fun e _ ↦ G.edgeEnds_not_isDiag e, ?_⟩
    intro v e heM heInc f hfM hfInc
    have hv := h v
    rw [Pi.one_apply, Finset.sum_le_one_iff] at hv
    exact (hv e f
      ((Graph.mem_incidentEdges G).2 ⟨v, by simp, heInc⟩)
      ((Graph.mem_incidentEdges G).2 ⟨v, by simp, hfInc⟩)
      ((matchingMultiplicity_ne_zero_iff M e).2 heM)
      ((matchingMultiplicity_ne_zero_iff M f).2 hfM)).1

/-- In a unit-capacity multiset matching, every actual edge has multiplicity at most one. -/
theorem IsCapacitatedMatching.apply_le_one (hx : G.IsCapacitatedMatching 1 x) (e : E(G)) :
    x e ≤ 1 := by
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet e.2
  let u' : V(G) := ⟨u, huv.left_mem⟩
  have he : e ∈ G.incidentEdges {u'} :=
    (Graph.mem_incidentEdges G).2 ⟨u', by simp, huv.inc_left⟩
  exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) he).trans (hx u')

/-- The selected support of a unit-capacity edge multiplicity. -/
noncomputable def unitSupport (x : E(G) → ℕ) : Finset E(G) := by
  classical
  exact Finset.univ.filter fun e ↦ x e = 1

@[simp]
theorem mem_unitSupport {x : E(G) → ℕ} {e : E(G)} :
    e ∈ G.unitSupport x ↔ x e = 1 := by
  classical
  simp [unitSupport]

/-- The unit multiplicity of the support of a unit-capacity multiset matching recovers its
original multiplicity. -/
theorem IsCapacitatedMatching.matchingMultiplicity_unitSupport
    (hx : G.IsCapacitatedMatching 1 x) :
    G.matchingMultiplicity (G.unitSupport x) = x := by
  funext e
  have hle := hx.apply_le_one e
  by_cases h : x e = 1
  · calc
      G.matchingMultiplicity (G.unitSupport x) e = 1 :=
        (matchingMultiplicity_eq_one_iff _ _).2 (mem_unitSupport.2 h)
      _ = x e := h.symm
  · have hz : x e = 0 := by omega
    calc
      G.matchingMultiplicity (G.unitSupport x) e = 0 :=
        (matchingMultiplicity_eq_zero_iff _ _).2 (by simpa only [mem_unitSupport])
      _ = x e := hz.symm

/-- A unit-capacity multiset matching on a loopless graph determines an ordinary matching by
taking the edges of multiplicity one. -/
theorem IsCapacitatedMatching.isMatching_unitSupport [G.Loopless]
    (hx : G.IsCapacitatedMatching 1 x) : G.IsMatching (G.unitSupport x) := by
  rw [isMatching_iff_isCapacitatedMatching_matchingMultiplicity,
    hx.matchingMultiplicity_unitSupport]
  exact hx

/-- Ordinary matchings in a finite loopless multigraph are equivalent to unit-capacity multiset
matchings. The equivalence retains each selected edge identity as multiplicity one. -/
@[expose] noncomputable def matchingEquivUnitCapacitated [G.Loopless] :
    {M : Finset E(G) // G.IsMatching M} ≃
      {x : E(G) → ℕ // G.IsCapacitatedMatching 1 x} where
  toFun M := ⟨G.matchingMultiplicity M,
    (G.isMatching_iff_isCapacitatedMatching_matchingMultiplicity M).1 M.2⟩
  invFun x := ⟨G.unitSupport x, x.2.isMatching_unitSupport⟩
  left_inv M := by
    apply Subtype.ext
    ext e
    simp only [mem_unitSupport, matchingMultiplicity_eq_one_iff]
  right_inv x := by
    apply Subtype.ext
    exact x.2.matchingMultiplicity_unitSupport

@[simp]
theorem matchingEquivUnitCapacitated_apply [G.Loopless]
    (M : {M : Finset E(G) // G.IsMatching M}) :
    (G.matchingEquivUnitCapacitated M : E(G) → ℕ) = G.matchingMultiplicity M := by
  rfl

@[simp]
theorem matchingEquivUnitCapacitated_symm_apply [G.Loopless]
    (x : {x : E(G) → ℕ // G.IsCapacitatedMatching 1 x}) :
    (G.matchingEquivUnitCapacitated.symm x : Finset E(G)) = G.unitSupport x := by
  rfl

namespace IsCapacitatedMatching

/-- Lowering the multiplicities or raising the capacities preserves multiset capacitated matchings.
In particular, restricting a multiset capacitated matching to a set of edges gives one. -/
theorem mono (hx : G.IsCapacitatedMatching b x) (hyx : y ≤ x) (hb : b ≤ b') :
    G.IsCapacitatedMatching b' y :=
  fun v ↦ ((sum_le_sum fun e _ ↦ hyx e).trans (hx v)).trans (hb v)

/-- The sum of two multiset capacitated matchings is one for the sum of their capacities. -/
theorem add (hx : G.IsCapacitatedMatching b x) (hy : G.IsCapacitatedMatching b' y) :
    G.IsCapacitatedMatching (b + b') (x + y) :=
  fun v ↦ by simpa [sum_add_distrib] using add_le_add (hx v) (hy v)

/-- A multiset capacitated matching in a bipartite multigraph has size `b(L)` exactly when it
saturates every vertex of `L`. -/
theorem sum_eq_sum_left_iff (hx : G.IsCapacitatedMatching b x) {L R : Finset V(G)}
    (hLR : G.IsBipartition L R) :
    ∑ e, x e = ∑ v ∈ L, b v ↔ ∀ v ∈ L, ∑ e ∈ G.incidentEdges {v}, x e = b v := by
  rw [← hLR.sum_sum_incidentEdges_left x]
  exact sum_eq_sum_iff_of_le fun v _ ↦ isCapacitatedMatching_def.1 hx v

/-- **Weak duality for multiset capacitated matchings.** The size of a multiset capacitated
matching is at most the weight of any vertex cover. -/
theorem sum_le_sum_of_isVertexCover (hx : G.IsCapacitatedMatching b x) {C : Finset V(G)}
    (hC : G.IsVertexCover (C : Set V(G))) :
    ∑ e, x e ≤ ∑ v ∈ C, b v := by
  classical
  calc ∑ e, x e ≤ ∑ e : E(G), ∑ v ∈ C with G.Inc e.1 v.1, x e := sum_le_sum fun e _ ↦ by
        -- Some vertex of the cover is incident with `e`.
        obtain ⟨v, hv, he⟩ := hC.exists_mem_inc e
        exact single_le_sum (f := fun _ ↦ x e) (fun _ _ ↦ Nat.zero_le _)
          (mem_filter.2 ⟨hv, he⟩)
    _ = ∑ v ∈ C, ∑ e ∈ G.incidentEdges {v}, x e :=
        (G.sum_sum_incidentEdges_eq_sum_sum_filter_inc C x).symm
    _ ≤ ∑ v ∈ C, b v := sum_le_sum fun v _ ↦ hx v

end IsCapacitatedMatching

/-! ### Kőnig's theorem -/

/-- **Kőnig's theorem for multiset capacitated matchings.** Let `L` and `R` form a bipartition of a
multigraph with finitely many actual edges, and let `b v : ℕ` be a capacity on every actual vertex.
Some multiset capacitated matching `x` and some vertex cover `C` satisfy
`∑ e, x e = ∑ v ∈ C, b v`. By `Graph.IsCapacitatedMatching.sum_le_sum_of_isVertexCover`, the
matching is then largest and the cover of least weight. -/
theorem IsBipartition.exists_isCapacitatedMatching_isVertexCover_sum_eq {L R : Finset V(G)}
    (hLR : G.IsBipartition L R) (b : V(G) → ℕ) :
    ∃ (x : E(G) → ℕ) (C : Finset V(G)), G.IsCapacitatedMatching b x ∧
      G.IsVertexCover (C : Set V(G)) ∧ ∑ e, x e = ∑ v ∈ C, b v := by
  classical
  have := hLR.finite
  -- One arrow for every actual edge, from its end in `L` to its end in `R`.
  let Q (y z : V(G)) : Type v := {e : E(G) // G.IsLink e y z ∧ y ∈ L}
  obtain ⟨k, s, t, P, X, hs, ht, -, -, hP, hX, hk⟩ :=
    exists_paths_setSeparator_sum_eq (Q := Q) b L R
  -- Every member of the packing joins `L` to `R`, so it traverses an arrow. Choose one, from
  -- `src i` to `tgt i`, along the edge `edge i`.
  have hst (i : Fin k) : s i ≠ t i := fun h ↦ disjoint_left.1 hLR.disjoint (hs i) (h ▸ ht i)
  have harrow (i : Fin k) : ∃ (y z : V(G)) (e : E(G)) (he : G.IsLink e y z ∧ y ∈ L),
      (⟨y, z, e, he⟩ : Σ y z, Q y z) ∈ (P i).arrows := by
    obtain ⟨⟨y, z, e, he⟩, h⟩ := List.exists_mem_of_ne_nil _ ((P i).arrows_ne_nil (hst i))
    exact ⟨y, z, e, he, h⟩
  choose src tgt edge hedge hf using harrow
  refine ⟨fun e ↦ #{i | edge i = e}, X, fun v ↦ ?_, isVertexCover_def.2 fun e y z he ↦ ?_, ?_⟩
  · -- The members counted at `v` are members through `v`: both ends of the edge of the arrow
    -- are vertices of the member.
    rw [sum_card_fiberwise_eq_card_filter]
    refine (card_le_card fun i hi ↦ ?_).trans (hP v)
    simp only [mem_filter, mem_univ, true_and, mem_incidentEdges, mem_singleton,
      exists_eq_left] at hi ⊢
    rcases hi.eq_or_eq_of_isLink (hedge i).1 with h | h
    · exact Subtype.ext h ▸ (P i).source_mem_vertices_of_mem_arrows (hf i)
    · rw [Subtype.ext h, ArrowWalk.vertices_eq_cons_map_target_arrows]
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun a ↦ a.2.1) (hf i))
  · -- The one-arrow walk along `e` meets the separator.
    wlog hy : y ∈ L generalizing y z
    · exact (this z y he.symm (hLR.notMem_left_iff.1 hy |> hLR.mem_left_of_isLink he)).symm
    by_contra! h
    refine hX y hy z (hLR.mem_right_of_isLink he hy) <| reachableAvoiding_def.2
      ⟨(ArrowWalk.nil y).cons ⟨⟨e, he.edge_mem⟩, he, hy⟩, fun w hw ↦ ?_⟩
    simp only [ArrowWalk.vertices_cons, ArrowWalk.vertices_nil, List.concat_eq_append,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [h.1, h.2]
  · rw [hk, ← card_eq_sum_card_fiberwise (by simp), card_univ, Fintype.card_fin]

end Graph
