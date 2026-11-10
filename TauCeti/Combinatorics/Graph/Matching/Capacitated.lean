/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Bipartition
public import TauCeti.Combinatorics.Graph.Matching.Basic
public import TauCeti.Combinatorics.Network.Menger.SetToSet
import Mathlib.Algebra.GroupWithZero.Indicator

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
* `Graph.matchingEquivUnitCapacitated`: in a loopless multigraph, ordinary matchings correspond to
  unit-capacity multiset matchings through their characteristic functions.

## Main results

* `Graph.IsCapacitatedMatching.sum_le_sum_of_isVertexCover`: **weak duality**, the size of a
  multiset capacitated matching is at most the weight of any vertex cover.
* `Graph.IsCapacitatedMatching.isMatching`: in a loopless multigraph, the edges used by a multiset
  capacitated matching for unit capacities form a matching, and a perfect one when every actual
  vertex is used exactly once (`Graph.isPerfectMatching_of_sum_incidentEdges_eq_one`).
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

/-- In a loopless multigraph, ordinary matchings are exactly unit-capacity multiset matchings
whose multiplicities are the characteristic function of the selected edges. -/
theorem isMatching_iff_isCapacitatedMatching_indicator [G.Loopless] (M : Set E(G)) :
    G.IsMatching M ↔ G.IsCapacitatedMatching 1 (M.indicator 1) := by
  rw [isMatching_def, isCapacitatedMatching_def]
  have hmem {e : E(G)} (he : M.indicator (1 : E(G) → ℕ) e ≠ 0) : e ∈ M := by
    by_contra h
    exact he (Set.indicator_of_notMem h _)
  constructor
  · rintro ⟨-, h⟩ v
    rw [Pi.one_apply, Finset.sum_le_one_iff]
    intro e f he hf he0 hf0
    obtain ⟨w, hw, hev⟩ := (mem_incidentEdges G).1 he
    obtain ⟨z, hz, hfv⟩ := (mem_incidentEdges G).1 hf
    rw [Finset.mem_singleton] at hw hz
    subst w z
    refine ⟨by_contra fun hef ↦ h e (hmem he0) f (hmem hf0) hef v ⟨hev, hfv⟩, ?_⟩
    exact Set.indicator_of_mem (hmem he0) _
  · intro h
    refine ⟨fun e _ x ↦ G.not_isLoopAt e x, fun e he f hf hef v ⟨hev, hfv⟩ ↦ hef ?_⟩
    let v' : V(G) := ⟨v, hev.vertex_mem⟩
    have hv := h v'
    rw [Pi.one_apply, Finset.sum_le_one_iff] at hv
    refine (hv e f ((mem_incidentEdges G).2 ⟨v', by simp, hev⟩)
      ((mem_incidentEdges G).2 ⟨v', by simp, hfv⟩) ?_ ?_).1 <;>
      simp [Set.indicator_of_mem, *]

/-- In a unit-capacity multiset matching, every actual edge has multiplicity at most one. -/
theorem IsCapacitatedMatching.apply_le_one (hx : G.IsCapacitatedMatching 1 x) (e : E(G)) :
    x e ≤ 1 := by
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet e.2
  let u' : V(G) := ⟨u, huv.left_mem⟩
  have he : e ∈ G.incidentEdges {u'} :=
    (mem_incidentEdges G).2 ⟨u', by simp, huv.inc_left⟩
  exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) he).trans (hx u')

/-- The indicator of the edges of multiplicity one in a unit-capacity multiset matching recovers
its multiplicities. -/
theorem IsCapacitatedMatching.indicator_setOf_eq_one (hx : G.IsCapacitatedMatching 1 x) :
    {e | x e = 1}.indicator 1 = x := by
  funext e
  by_cases h : x e = 1
  · rw [Set.indicator_of_mem h, Pi.one_apply, h]
  · rw [Set.indicator_of_notMem h]
    have := hx.apply_le_one e
    omega

/-- A unit-capacity multiset matching on a loopless graph determines an ordinary matching by
taking the edges of multiplicity one. -/
theorem IsCapacitatedMatching.isMatching_setOf_eq_one [G.Loopless]
    (hx : G.IsCapacitatedMatching 1 x) : G.IsMatching {e | x e = 1} := by
  rw [isMatching_iff_isCapacitatedMatching_indicator, hx.indicator_setOf_eq_one]
  exact hx

/-- Ordinary matchings in a finite loopless multigraph are equivalent to unit-capacity multiset
matchings. The equivalence retains each selected edge identity as multiplicity one. -/
noncomputable def matchingEquivUnitCapacitated [G.Loopless] :
    {M : Set E(G) // G.IsMatching M} ≃ {x : E(G) → ℕ // G.IsCapacitatedMatching 1 x} where
  toFun M := ⟨M.1.indicator 1, (isMatching_iff_isCapacitatedMatching_indicator M.1).1 M.2⟩
  invFun x := ⟨{e | x.1 e = 1}, x.2.isMatching_setOf_eq_one⟩
  left_inv M := by
    ext e
    exact Set.indicator_eq_one_iff_mem ℕ
  right_inv x := Subtype.ext x.2.indicator_setOf_eq_one

@[simp]
theorem matchingEquivUnitCapacitated_apply [G.Loopless] (M : {M : Set E(G) // G.IsMatching M}) :
    (G.matchingEquivUnitCapacitated M : E(G) → ℕ) = M.1.indicator 1 :=
  (rfl)

@[simp]
theorem matchingEquivUnitCapacitated_symm_apply [G.Loopless]
    (x : {x : E(G) → ℕ // G.IsCapacitatedMatching 1 x}) :
    (G.matchingEquivUnitCapacitated.symm x : Set E(G)) = {e | x.1 e = 1} :=
  (rfl)

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

/-- In a loopless multigraph, the edges used by a multiset capacitated matching for the unit
capacities form a matching. -/
theorem isMatching [G.Loopless] (hx : G.IsCapacitatedMatching 1 x) :
    G.IsMatching {e | x e ≠ 0} := by
  classical
  refine isMatching_def.2 ⟨fun e _ v ↦ G.not_isLoopAt _ v, fun e he f hf hef v ⟨hev, hfv⟩ ↦ ?_⟩
  -- Two distinct used edges at `v` would use `v` at least twice.
  have := (sum_pair (f := x) hef).symm.trans_le <|
    sum_le_sum_of_subset (f := x) (t := G.incidentEdges {⟨v, hev.vertex_mem⟩}) <| by
      simp [insert_subset_iff, hev, hfv]
  have := hx ⟨v, hev.vertex_mem⟩
  simp only [Set.mem_ofPred_eq, Pi.one_apply] at he hf this
  omega

end IsCapacitatedMatching

/-- In a loopless multigraph, if edge multiplicities `x` use every actual vertex exactly once, then
the edges they use form a perfect matching. -/
theorem isPerfectMatching_of_sum_incidentEdges_eq_one [G.Loopless]
    (hx : ∀ v, ∑ e ∈ G.incidentEdges {v}, x e = 1) :
    G.IsPerfectMatching {e | x e ≠ 0} := by
  refine isPerfectMatching_def.2 ⟨IsCapacitatedMatching.isMatching fun v ↦ (hx v).le, fun v ↦ ?_⟩
  obtain ⟨e, he, hxe⟩ := exists_ne_zero_of_sum_ne_zero ((hx v).trans_ne one_ne_zero)
  exact ⟨e, hxe, by simpa using he⟩

/-! ### Unit capacities and ordinary matchings -/

namespace IsMatching

/-- An ordinary matching, represented by a finite set of actual edges, is a multiset
capacitated matching for unit vertex capacities when its selected edges have multiplicity one. -/
theorem isCapacitatedMatching_indicator {M : Finset E(G)} (hM : G.IsMatching (M : Set E(G))) :
    G.IsCapacitatedMatching (fun _ ↦ 1) ((M : Set E(G)).indicator fun _ ↦ 1) := by
  classical
  rw [isCapacitatedMatching_def]
  intro x
  calc
    ∑ e ∈ G.incidentEdges {x}, (M : Set E(G)).indicator (fun _ ↦ 1) e =
        ∑ e ∈ G.incidentEdges {x}, if e ∈ M then 1 else 0 :=
      sum_congr rfl fun e _ ↦ Set.indicator_apply _ _ _
    _ = ((G.incidentEdges {x}).filter (· ∈ M)).card :=
      sum_boole (R := ℕ) (· ∈ M) (G.incidentEdges {x})
    _ ≤ 1 := card_le_one.mpr fun e he f hf ↦ by
      obtain ⟨heinc, heM⟩ := mem_filter.1 he
      obtain ⟨hfinc, hfM⟩ := mem_filter.1 hf
      obtain ⟨y, hy, hey⟩ := (mem_incidentEdges G).1 heinc
      obtain ⟨z, hz, hfz⟩ := (mem_incidentEdges G).1 hfinc
      exact hM.eq_of_inc heM hfM (Finset.mem_singleton.mp hy ▸ hey)
        (Finset.mem_singleton.mp hz ▸ hfz)

end IsMatching

namespace IsCapacitatedMatching

/-- The sum of the multiplicities in a unit-capacitated matching is the cardinality of its
positive support. -/
theorem sum_eq_card_support {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching (fun _ ↦ 1) x) :
    ∑ e, x e = (Finset.univ.filter fun e ↦ x e ≠ 0).card := by
  classical
  calc
    ∑ e, x e = ∑ e, if x e ≠ 0 then 1 else 0 := sum_congr rfl fun e _ ↦ by
      have hle := hx.apply_le_one e
      split_ifs with he
      · omega
      · simpa using he
    _ = (Finset.univ.filter fun e ↦ x e ≠ 0).card := by
      exact sum_boole (R := ℕ) (fun e ↦ x e ≠ 0) univ

/-- In a loopless graph, the positive support of a unit-capacitated matching is an ordinary
matching. -/
theorem support_isMatching {x : E(G) → ℕ} (hx : G.IsCapacitatedMatching (fun _ ↦ 1) x)
    (hG : G.Loopless) : G.IsMatching ({e | x e ≠ 0} : Set E(G)) := by
  classical
  rw [isMatching_def]
  refine ⟨fun e _ y ↦ hG.not_isLoopAt e y, fun e he f hf hef y hinc ↦ ?_⟩
  have hey : e ∈ G.incidentEdges {⟨y, hinc.1.vertex_mem⟩} :=
    (mem_incidentEdges G).2 ⟨⟨y, hinc.1.vertex_mem⟩, mem_singleton_self _, hinc.1⟩
  have hfy : f ∈ G.incidentEdges {⟨y, hinc.1.vertex_mem⟩} :=
    (mem_incidentEdges G).2 ⟨⟨y, hinc.1.vertex_mem⟩, mem_singleton_self _, hinc.2⟩
  have hpair : ∑ a ∈ {e, f}, x a ≤ 1 :=
    (sum_le_sum_of_subset (insert_subset_iff.2 ⟨hey, singleton_subset_iff.2 hfy⟩)).trans
      (isCapacitatedMatching_def.1 hx ⟨y, hinc.1.vertex_mem⟩)
  rw [sum_pair hef] at hpair
  have he' : x e ≠ 0 := by simpa only [Set.mem_ofPred_eq] using he
  have hf' : x f ≠ 0 := by simpa only [Set.mem_ofPred_eq] using hf
  omega

/-- The finite positive support of a unit-capacitated matching in a loopless graph is an
ordinary matching. -/
theorem supportFinset_isMatching {x : E(G) → ℕ}
    (hx : G.IsCapacitatedMatching (fun _ ↦ 1) x) (hG : G.Loopless) :
    G.IsMatching (↑(Finset.univ.filter fun e ↦ x e ≠ 0) : Set E(G)) := by
  have hset : (↑(Finset.univ.filter fun e ↦ x e ≠ 0) : Set E(G)) = {e | x e ≠ 0} := by
    ext
    simp
  rw [hset]
  exact hx.support_isMatching hG

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
