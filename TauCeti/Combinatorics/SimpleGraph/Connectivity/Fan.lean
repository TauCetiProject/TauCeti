/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.VertexConnectivity

/-!
# The fan lemma

Let `G` be a simple graph, `x` a vertex and `U` a finite set of vertices not containing `x`. A
*fan* from `x` to `U` is a family of paths, the `i`-th from `x` to a vertex `u i ∈ U`, whose other
vertices lie outside `U`, and any two of which share only the vertex `x`; in particular their ends
`u i` are distinct. This file proves the fan form of Menger's theorem on a finite vertex type: the
largest fan from `x` to `U` has as many paths as the least number of vertices other than `x` that
meet every walk from `x` to a vertex of `U`.

The **fan lemma** follows: in a `k`-vertex-connected graph on a finite vertex type, a vertex `x`
outside a set `U` of at least `k` vertices is joined to `U` by a fan of `k` paths. More generally,
it suffices that `x` be `k`-vertex-reachable from every vertex of `U`. Fans are the tool by which
cycles through prescribed vertices are built in highly connected graphs.

## Main results

* `SimpleGraph.card_le_card_of_fan`: weak duality: a fan from `x` to `U` has at most as many paths
  as any set of vertices other than `x` meeting every walk from `x` to `U`. No finiteness is needed.
* `SimpleGraph.exists_fan_separator_card_eq`: the fan form of **Menger's theorem**, in witness
  form: some fan and some such separator have the same size.
* `SimpleGraph.forall_exists_walk_iff_exists_fan`: its predicate form: deleting fewer than `k`
  vertices other than `x` always leaves a walk from `x` to `U` exactly when there is a fan of `k`
  paths from `x` to `U`.
* `SimpleGraph.exists_fan_of_forall_isVertexReachable` and
  `SimpleGraph.IsVertexConnected.exists_fan`: the **fan lemma**.

## Implementation notes

The witness form is derived from the vertex-capacitated set-to-set form of Menger's theorem,
`SimpleGraph.exists_paths_setSeparator_sum_eq`, between the neighbours of `x` and `U`, with
capacity `0` at `x` and `1` at every other vertex. The capacities make the paths pairwise
vertex-disjoint and keep them away from `x`, so prefixing each with its first edge from `x`
gives a fan; a path that already starts in `U` is replaced by that single edge. A separator of
this capacitated problem, with `x` removed, meets every walk from `x` to `U`: such a walk contains
a path from `x` to `U`, whose part after its first edge is a walk from a neighbour of `x` to `U`
avoiding `x`.

## References

* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017,
  Corollary 3.3.4.
-/

public section

open Finset

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {x : V} {U : Finset V}

/-- **Weak duality for fans.** A family of walks, the `i`-th from `x` to `u i ∈ U`, any two of which
share only the vertex `x`, has at most `#X` members, for every set `X` of vertices not containing
`x` that meets every walk from `x` to a vertex of `U`. No finiteness assumption on `V` is
needed. -/
theorem card_le_card_of_fan {ι : Type*} [Fintype ι] {u : ι → V} {P : ∀ i, G.Walk x (u i)}
    (hu : ∀ i, u i ∈ U) (hP : Pairwise fun i j ↦ ∀ v ∈ (P i).support, v ∈ (P j).support → v = x)
    {X : Finset V} (hxX : x ∉ X) (hX : ∀ y ∈ U, ∀ p : G.Walk x y, ∃ v ∈ p.support, v ∈ X) :
    Fintype.card ι ≤ #X := by
  choose v hv hvX using fun i ↦ hX _ (hu i) (P i)
  have hinj : Function.Injective fun i ↦ (⟨v i, hvX i⟩ : X) := fun i j hij ↦ by
    by_contra hne
    rw [Subtype.mk.injEq] at hij
    exact hxX (hP hne (v i) (hv i) (hij ▸ hv j) ▸ hvX i)
  simpa using Fintype.card_le_of_injective _ hinj

/-- A path `p` from a neighbour `a` of `x` to a vertex `b ∈ U`, avoiding `x`, with no vertex other
than `a` and `b` in `U`, yields a path from `x` to a vertex `y ∈ U` of `p` with no other vertex in
`U` and no vertex outside `p` other than `x`: the edge from `x` to `a` if `a ∈ U`, and that edge
followed by `p` otherwise. -/
private theorem exists_walk_of_isPath {a b : V} (hx : x ∉ U) (ha : G.Adj x a) (hb : b ∈ U)
    {p : G.Walk a b} (hp : p.IsPath) (hxp : x ∉ p.support)
    (hint : ∀ v ∈ p.support, v ≠ a → v ≠ b → v ∉ U) :
    ∃ (y : V) (F : G.Walk x y), y ∈ U ∧ y ∈ p.support ∧ F.IsPath ∧
      (∀ v ∈ F.support, v ≠ y → v ∉ U) ∧ ∀ v ∈ F.support, v = x ∨ v ∈ p.support := by
  by_cases haU : a ∈ U
  · refine ⟨a, ha.toWalk, haU, p.start_mem_support, ha.isPath_toWalk, fun v hv hva ↦ ?_,
      fun v hv ↦ ?_⟩ <;>
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    · obtain rfl | rfl := hv
      exacts [hx, absurd rfl hva]
    · obtain rfl | rfl := hv
      exacts [.inl rfl, .inr p.start_mem_support]
  · refine ⟨b, .cons ha p, hb, p.end_mem_support, (Walk.cons_isPath_iff _ _).2 ⟨hp, hxp⟩,
      fun v hv hvb ↦ ?_, fun v hv ↦ ?_⟩ <;>
    rw [Walk.support_cons, List.mem_cons] at hv
    · obtain rfl | hv := hv
      · exact hx
      · obtain rfl | hva := eq_or_ne v a
        exacts [haU, hint v hv hva hvb]
    · exact hv

/-- **Menger's theorem for fans.** Let `x` be a vertex outside a set `U` of vertices of a simple
graph on a finite vertex type. Some family of `k` paths, the `i`-th from `x` to `u i ∈ U` with its
other vertices outside `U`, any two of which share only the vertex `x`, and some set of `k`
vertices other than `x` meeting every walk from `x` to a vertex of `U` exist. By
`SimpleGraph.card_le_card_of_fan`, the fan is then largest and the separator smallest. -/
theorem exists_fan_separator_card_eq [Finite V] (hx : x ∉ U) :
    ∃ (k : ℕ) (u : Fin k → V) (P : ∀ i, G.Walk x (u i)) (X : Finset V),
      Function.Injective u ∧ (∀ i, u i ∈ U) ∧ (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).support, v ≠ u i → v ∉ U) ∧
      (Pairwise fun i j ↦ ∀ v ∈ (P i).support, v ∈ (P j).support → v = x) ∧
      x ∉ X ∧ (∀ y ∈ U, ∀ p : G.Walk x y, ∃ v ∈ p.support, v ∈ X) ∧ #X = k := by
  classical
  have := Fintype.ofFinite V
  -- Vertex-capacitated set-to-set Menger from the neighbours of `x` to `U`, where `x` has
  -- capacity `0` and every other vertex capacity `1`.
  obtain ⟨k, a, b, P, X, ha, hb, hP, hint, hPv, hX, hk⟩ :=
    exists_paths_setSeparator_sum_eq (G := G) (fun v ↦ if v = x then 0 else 1)
      {v | G.Adj x v} U
  simp only [mem_filter, mem_univ, true_and] at ha hX
  have hxP (i : Fin k) : x ∉ (P i).support := by
    have h0 : #{i | x ∈ (P i).support} = 0 := by simpa using hPv x
    exact filter_eq_empty_iff.1 (card_eq_zero.1 h0) (mem_univ i)
  have hdisj : Pairwise fun i j ↦ ∀ v ∈ (P i).support, v ∉ (P j).support := by
    intro i j hij v hvi hvj
    have h1 : #{i | v ∈ (P i).support} ≤ 1 := by
      simpa [ne_of_mem_of_not_mem hvi (hxP i)] using hPv v
    exact h1.not_gt (one_lt_card.2 ⟨i, by simpa using hvi, j, by simpa using hvj, hij⟩)
  -- Prefix each path with its first edge from `x`, or replace it by that edge if it starts in `U`.
  choose u F hu huP hF hFU hFP using fun i ↦
    exists_walk_of_isPath hx (ha i) (hb i) (hP i) (hxP i)
      fun v hv hva hvb ↦ (hint i v hv hva hvb).2
  refine ⟨k, u, F, X.erase x, fun i j hij ↦ ?_, hu, hF, hFU, fun i j hij v hvi hvj ↦ ?_,
    notMem_erase x X, fun y hy p ↦ ?_, ?_⟩
  · by_contra hne
    exact hdisj hne (u i) (huP i) (hij ▸ huP j)
  · obtain hv | hv := hFP i v hvi
    · exact hv
    · obtain hv' | hv' := hFP j v hvj
      · exact hv'
      · exact absurd hv' (hdisj hij v hv)
  · -- A walk from `x` to `y ∈ U` contains a path from `x` to `y`; after its first edge, that path
    -- runs from a neighbour of `x` to `U` avoiding `x`, so it meets `X` away from `x`.
    obtain ⟨z, h, q, hq⟩ := Walk.exists_eq_cons_of_ne (ne_of_mem_of_not_mem hy hx).symm p.bypass
    have hxq : x ∉ q.support := ((Walk.cons_isPath_iff h q).1 (hq ▸ p.bypass_isPath)).2
    obtain ⟨v, hv, hvX⟩ := hX z h y hy q
    have hvp : v ∈ p.support :=
      p.support_bypass_subset_support (hq ▸ List.mem_cons_of_mem _ hv)
    exact ⟨v, hvp, mem_erase.2 ⟨ne_of_mem_of_not_mem hv hxq, hvX⟩⟩
  · simp [← hk, sum_ite, filter_ne']

/-- **Menger's theorem for fans, predicate form.** Let `x` be a vertex outside a set `U` of vertices
of a simple graph on a finite vertex type. For every set `X` of fewer than `k` vertices other than
`x`, some walk from `x` to a vertex of `U` avoids `X`, exactly when there are `k` paths, the `i`-th
from `x` to `u i ∈ U` with its other vertices outside `U`, any two of which share only the vertex
`x`. -/
theorem forall_exists_walk_iff_exists_fan [Finite V] (hx : x ∉ U) (k : ℕ) :
    (∀ X : Finset V, #X < k → x ∉ X → ∃ y ∈ U, ∃ p : G.Walk x y, ∀ v ∈ p.support, v ∉ X) ↔
      ∃ (u : Fin k → V) (P : ∀ i, G.Walk x (u i)), Function.Injective u ∧ (∀ i, u i ∈ U) ∧
        (∀ i, (P i).IsPath) ∧ (∀ i, ∀ v ∈ (P i).support, v ≠ u i → v ∉ U) ∧
        Pairwise fun i j ↦ ∀ v ∈ (P i).support, v ∈ (P j).support → v = x := by
  refine ⟨fun h ↦ ?_, fun ⟨u, P, _, hu, _, _, hP⟩ X hX hxX ↦ ?_⟩
  · obtain ⟨n, u, P, X, hinj, hu, hP, hint, hdisj, hxX, hX, rfl⟩ :=
      exists_fan_separator_card_eq (G := G) hx
    -- The separator `X` has at least `k` vertices, so the fan has at least `k` paths; keep the
    -- first `k` of them.
    have hkn : k ≤ #X := by
      by_contra! hlt
      obtain ⟨y, hy, p, hp⟩ := h X hlt hxX
      obtain ⟨v, hv, hvX⟩ := hX y hy p
      exact hp v hv hvX
    exact ⟨u ∘ Fin.castLE hkn, fun i ↦ P _, hinj.comp (Fin.castLE_injective hkn), fun i ↦ hu _,
      fun i ↦ hP _, fun i ↦ hint _, fun i j hij ↦ hdisj ((Fin.castLE_injective hkn).ne hij)⟩
  · by_contra h
    push Not at h
    exact hX.not_ge (by simpa using card_le_card_of_fan hu hP hxX h)

/-- **The fan lemma.** Let `x` be a vertex outside a set `U` of at least `k` vertices of a simple
graph on a finite vertex type, and suppose that `x` is `k`-vertex-reachable from every vertex of
`U`. Then there are `k` paths, the `i`-th from `x` to `u i ∈ U` with its other vertices outside
`U`, any two of which share only the vertex `x`. -/
theorem exists_fan_of_forall_isVertexReachable [Finite V] {k : ℕ} (hx : x ∉ U) (hU : k ≤ #U)
    (h : ∀ y ∈ U, G.IsVertexReachable k x y) :
    ∃ (u : Fin k → V) (P : ∀ i, G.Walk x (u i)), Function.Injective u ∧ (∀ i, u i ∈ U) ∧
      (∀ i, (P i).IsPath) ∧ (∀ i, ∀ v ∈ (P i).support, v ≠ u i → v ∉ U) ∧
      Pairwise fun i j ↦ ∀ v ∈ (P i).support, v ∈ (P j).support → v = x := by
  refine (forall_exists_walk_iff_exists_fan hx k).1 fun X hX hxX ↦ ?_
  obtain ⟨y, hy, hyX⟩ := exists_mem_notMem_of_card_lt_card (hX.trans_le hU)
  obtain ⟨p, hp⟩ := isVertexReachable_iff_exists_walk.1 (h y hy)
    (by rwa [Set.encard_coe_eq_coe_finsetCard, Nat.cast_lt]) hxX hyX
  exact ⟨y, hy, p, hp⟩

/-- **The fan lemma.** In a `k`-vertex-connected simple graph on a finite vertex type, a vertex `x`
outside a set `U` of at least `k` vertices is joined to `U` by `k` paths, the `i`-th from `x` to
`u i ∈ U` with its other vertices outside `U`, any two of which share only the vertex `x`. -/
theorem IsVertexConnected.exists_fan [Finite V] {k : ℕ} (h : G.IsVertexConnected k) (hx : x ∉ U)
    (hU : k ≤ #U) :
    ∃ (u : Fin k → V) (P : ∀ i, G.Walk x (u i)), Function.Injective u ∧ (∀ i, u i ∈ U) ∧
      (∀ i, (P i).IsPath) ∧ (∀ i, ∀ v ∈ (P i).support, v ≠ u i → v ∉ U) ∧
      Pairwise fun i j ↦ ∀ v ∈ (P i).support, v ∈ (P j).support → v = x :=
  exists_fan_of_forall_isVertexReachable hx hU fun y _ ↦ h.isVertexReachable x y

end SimpleGraph
