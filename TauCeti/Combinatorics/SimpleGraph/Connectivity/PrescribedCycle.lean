/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Fan
public import TauCeti.Combinatorics.SimpleGraph.Paths
import TauCeti.Data.Finset.Card

/-!
# Cycles through prescribed vertices

This file proves **Dirac's theorem** on cycles through prescribed vertices: for `k ≥ 2`, every
set of at most `k` vertices of a `k`-vertex-connected simple graph on a finite vertex type lies on
a common cycle. No cyclic order of the prescribed vertices is imposed.

## Main results

* `SimpleGraph.Walk.IsCycle.exists_isCycle_forall_mem_support_insert`: for `2 ≤ k`, a cycle
  through a set `T` of fewer than `k` vertices can be replaced by a cycle through `T` and any
  vertex that is `k`-vertex-reachable from every vertex of the cycle.
* `SimpleGraph.IsVertexConnected.exists_isCycle_forall_mem_support`: **Dirac's theorem**.

## Implementation notes

Given a cycle `C` through `T` and a vertex `x` off `C`, the fan lemma
`SimpleGraph.exists_fan_of_forall_isVertexReachable` joins `x` to `min k |C|` distinct vertices
of `C` by paths meeting only at `x` and avoiding `C` otherwise. These ends cut `C` into as many
arcs, which outnumber the vertices of `T` not among the ends, so the interior of some arc between
two consecutive ends avoids `T`. Replacing that arc by the two fan paths to its ends gives the new
cycle. The arc is found by scanning the cycle, rotated to start at an end, for consecutive ends.
The path and cycle surgery used here is in `TauCeti.Combinatorics.SimpleGraph.Paths`.

## References

* G. A. Dirac, *In abstrakten Graphen vorhandene vollständige 4-Graphen und ihre Unterteilungen*,
  Math. Nachr. 22 (1960), 61–85.
* J. A. Bondy and U. S. R. Murty, *Graph Theory*, Graduate Texts in Mathematics 244, Springer,
  2008, Chapter 9.
-/

public section

open Finset

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

namespace Walk

/-- Let `c` be a cycle in a simple graph on a finite vertex type, through a set `T` of fewer than
`k` of its vertices, where `2 ≤ k`. If a vertex `x` is `k`-vertex-reachable from every vertex of
`c`, then `x` lies on a cycle through all of `T`. -/
theorem IsCycle.exists_isCycle_forall_mem_support_insert [Finite V] [DecidableEq V] {k : ℕ}
    {r x : V} {c : G.Walk r r} (hc : c.IsCycle) (hk : 2 ≤ k)
    (h : ∀ y ∈ c.support, G.IsVertexReachable k x y) {T : Finset V}
    (hT : ∀ v ∈ T, v ∈ c.support) (hTk : #T < k) :
    ∃ (u : V) (c' : G.Walk u u), c'.IsCycle ∧ ∀ v ∈ insert x T, v ∈ c'.support := by
  simp only [mem_insert, forall_eq_or_imp]
  by_cases hx : x ∈ c.support
  · exact ⟨r, c, hc, hx, hT⟩
  -- A fan from `x` to `min k |c|` distinct vertices of `c`; its set of ends is `F`.
  set U := c.support.toFinset with hU
  have hxU : x ∉ U := by simpa [U] using hx
  have hU2 : 2 ≤ #U := one_lt_card.2 ⟨r, by simp [U], c.snd, by simp [U, c.getVert_mem_support 1],
    (c.adj_snd hc.not_nil).ne⟩
  obtain ⟨u, P, hinj, huU, hP, hint, hdisj⟩ :=
    exists_fan_of_forall_isVertexReachable hxU (min_le_right k #U) fun y hy ↦
      (h y (by simpa [U] using hy)).anti (by exact_mod_cast min_le_left k #U)
  set F := univ.image u with hF
  have hFm : #F = min k #U := by
    rw [hF, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hFU : F ⊆ U := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := mem_image.1 hv
    exact huU i
  -- The ends outnumber the vertices of `T` that are not ends.
  have hTF : #(T \ F) < #F :=
    card_sdiff_lt_of_card_eq_min hFU (fun v hv ↦ by simpa [U] using hT v hv)
      (card_pos.1 (by omega)) hFm hTk
  -- Rotate `c` to start at an end, and cut it at an arc between two ends avoiding `T`.
  obtain ⟨r', hr'F, hr'⟩ : ∃ r' ∈ F, r' ∈ c.support :=
    ⟨u ⟨0, by omega⟩, mem_image_of_mem _ (mem_univ _), by simpa [U] using huU ⟨0, by omega⟩⟩
  obtain ⟨c', hc', hmem⟩ : ∃ c' : G.Walk r' r', c'.IsCycle ∧ ∀ v, v ∈ c'.support ↔ v ∈ c.support :=
    ⟨c.rotate r' hr', hc.rotate hr', fun v ↦ mem_support_rotate_iff ..⟩
  obtain ⟨a, b, W₁, A, W₂, rfl, ha, hb, hab, hA, hAi⟩ := hc'.exists_eq_append_append hr'F
    (fun v hv ↦ (hmem v).2 (by simpa [U] using hFU hv)) (hFm ▸ le_min hk hU2) hTF
  obtain ⟨i, -, rfl⟩ := mem_image.1 ha
  obtain ⟨j, -, rfl⟩ := mem_image.1 hb
  -- The rest `R` of the cycle, from `u j` back to `u i`, is a path through `T`.
  have hRc : ∀ v ∈ (W₂.append W₁).support, v ∈ U := by
    intro v hv
    rw [mem_support_append_iff] at hv
    rw [hU, List.mem_toFinset, ← hmem, mem_support_append_iff, mem_support_append_iff]
    tauto
  have hTR : ∀ v ∈ T, v ∈ (W₂.append W₁).support := fun v hv ↦
    mem_support_append_of_mem_support_append_append ((hmem v).2 (hT v hv)) fun hvA ↦ by
      by_contra! hvij
      exact hAi v hvA hvij.1 hvij.2 hv
  -- Close up the fan paths to `u j` and `u i` with `R`.
  have hcyc := (hP i).isCycle_append_append_reverse (hP j) (hc'.isPath_append_of_append_append hA)
    hab (hdisj fun hij ↦ hab (hij ▸ rfl))
    (fun v hvP hvR ↦ by_contra fun hv ↦ hint i v hvP hv (hRc v hvR))
    (fun v hvP hvR ↦ by_contra fun hv ↦ hint j v hvP hv (hRc v hvR))
  refine ⟨x, _, hcyc, start_mem_support _, fun v hv ↦ ?_⟩
  rw [mem_support_append_iff, mem_support_append_iff]
  exact .inl (.inr (hTR v hv))

end Walk

/-- **Dirac's theorem.** For `2 ≤ k`, every set of at most `k` vertices of a `k`-vertex-connected
simple graph on a finite vertex type lies on a common cycle. -/
theorem IsVertexConnected.exists_isCycle_forall_mem_support [Finite V] {k : ℕ} (hk : 2 ≤ k)
    (h : G.IsVertexConnected k) {S : Finset V} (hS : #S ≤ k) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ ∀ v ∈ S, v ∈ c.support := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    -- A `k`-vertex-connected graph has more than `k ≥ 2` vertices and is `2`-edge-connected.
    have h1 : (1 : ℕ∞) < k + 1 := by exact_mod_cast (show 1 < k + 1 by omega)
    have : Nontrivial V := (ENat.one_lt_card_iff_nontrivial V).1 (h1.trans_le h.add_one_le_card)
    obtain ⟨v, w, hvw⟩ := exists_pair_ne V
    obtain ⟨c, hc⟩ := exists_isCycle_of_two_le_isEdgeReachable hvw (by exact_mod_cast hk)
      (h.isEdgeConnected v w)
    exact ⟨v, c, hc, by simp⟩
  | insert x T hxT ih =>
    rw [card_insert_of_notMem hxT] at hS
    obtain ⟨r, c, hc, hT⟩ := ih (by omega)
    exact hc.exists_isCycle_forall_mem_support_insert hk (fun y _ ↦ h.isVertexReachable x y) hT
      (by omega)

end SimpleGraph
