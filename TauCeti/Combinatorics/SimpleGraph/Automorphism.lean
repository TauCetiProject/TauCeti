/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.Combinatorics.SimpleGraph.PathGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import TauCeti.GroupTheory.Perm.Basic

/-!
# Orbits of graph automorphisms on bipartite graphs, trees, and path graphs

An automorphism `f : G ≃g G` of a bipartite graph that fixes a vertex `c` cannot join two vertices
in the same `f`-orbit inside the connected component of `c`: adjacent reachable vertices lie in
opposite colour classes and therefore at unequal distances from `c`, whereas `f` preserves distance
from `c` and so `G.dist c` is constant on every `f`-orbit. On a tree, connectedness removes the
reachability hypothesis; in particular, if `G` is a locally finite tree possessing a vertex whose
degree occurs nowhere else in `G`, every automorphism fixes that vertex and every automorphism orbit
is an independent set.

On the path graph `SimpleGraph.pathGraph n`, no vertex has unique degree once `n = 2` or `4 ≤ n`;
its automorphism group consists of the identity and the reversal `TauCeti.pathGraphRevIso n` (which
fixes the central vertex when `n` is odd). Under reversal, every orbit on an odd path graph is still
an independent set, whereas on an even path graph `pathGraph (2 * n)` (`1 ≤ n`) the adjacent middle
pair `{n - 1, n}` is the unique orbit containing an edge.

## Main results

* `SimpleGraph.IsBipartite.dist_ne_of_adj`: in a bipartite graph, adjacent vertices reachable from
  `u` have distinct distances from `u`.
* `SimpleGraph.IsBipartite.not_adj_of_sameCycle_of_apply_eq`,
  `SimpleGraph.IsAcyclic.not_adj_of_sameCycle_of_apply_eq`, and
  `SimpleGraph.IsTree.not_adj_of_sameCycle_of_apply_eq`: an automorphism fixing a vertex has no
  edge inside any single orbit of its connected component (or anywhere in a tree).
* `SimpleGraph.Iso.apply_eq_of_degree_unique` and
  `SimpleGraph.IsTree.not_adj_of_sameCycle_of_degree_unique`: a vertex of unique degree is fixed by
  every automorphism, making every automorphism orbit on a locally finite tree independent.
* `SimpleGraph.Iso.eq_refl_of_pathGraph_apply_zero` and
  `SimpleGraph.Iso.eq_refl_or_eq_pathGraphRevIso`: every automorphism of `pathGraph n` is either
  `Iso.refl` or `TauCeti.pathGraphRevIso n`.
* `SimpleGraph.pathGraph_adj_rev_iff`,
  `SimpleGraph.not_pathGraph_adj_of_sameCycle_revPerm_of_odd`, and
  `SimpleGraph.sameCycle_revPerm_and_pathGraph_even_adj_iff`: adjacency along reversal orbits in odd
  and even path graphs.

## References

* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, §1.5–1.6.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## Bipartite graphs and trees with a fixed vertex -/

/-- **In a bipartite graph, adjacent vertices reachable from `u` lie at different distances from
`u`.** Shortest walks from `u` to `v` and `w` must have opposite parities because a `2`-colouring
assigns opposite colours to `v` and `w`. -/
theorem IsBipartite.dist_ne_of_adj (hG : G.IsBipartite) {u v w : V} (hadj : G.Adj v w)
    (hreach : G.Reachable u v) : G.dist u v ≠ G.dist u w := by
  obtain ⟨col⟩ := hG
  let c : G.Coloring Bool := G.recolorOfEquiv finTwoEquiv col
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := (hreach.trans hadj.reachable).exists_walk_length_eq_dist
  intro heq
  have hlen : p.length = q.length := hp.trans (heq.trans hq.symm)
  have hparity : (c u ↔ c v) ↔ (c u ↔ c w) := by
    rw [← c.even_length_iff_congr p, ← c.even_length_iff_congr q, hlen]
  have hcw : c v = c w := by
    revert hparity
    generalize c u = a, c v = b, c w = d
    decide +revert
  exact c.valid hadj hcw

/-- **An automorphism of a bipartite graph fixing `c` has no edge inside any orbit reachable from
`c`.** Distance from `c` is preserved by `f`, hence constant along `f`-orbits, while adjacent
reachable vertices cannot lie at equal distance from `c`. -/
theorem IsBipartite.not_adj_of_sameCycle_of_apply_eq (hG : G.IsBipartite) {f : G ≃g G}
    {c u v : V} (hc : f c = c) (hreach : G.Reachable c u)
    (hcyc : Equiv.Perm.SameCycle f.toEquiv u v) : ¬ G.Adj u v := by
  intro hadj
  have hinv : ∀ z : V, G.dist c (f.toEquiv z) = G.dist c z := fun z ↦ by
    calc G.dist c (f z)
      _ = G.dist (f c) (f z) := by rw [hc]
      _ = G.dist c z := f.dist_eq c z
  exact hG.dist_ne_of_adj hadj hreach (hcyc.apply_eq_of_apply_eq hinv)

/-- **An automorphism of a forest fixing `c` has no edge inside any orbit in the component of
`c`.** -/
theorem IsAcyclic.not_adj_of_sameCycle_of_apply_eq (hG : G.IsAcyclic) {f : G ≃g G}
    {c u v : V} (hc : f c = c) (hreach : G.Reachable c u)
    (hcyc : Equiv.Perm.SameCycle f.toEquiv u v) : ¬ G.Adj u v :=
  hG.isBipartite.not_adj_of_sameCycle_of_apply_eq hc hreach hcyc

/-- **An automorphism of a tree fixing a vertex has no edge inside any orbit** (every orbit of `f`
is an independent set). -/
theorem IsTree.not_adj_of_sameCycle_of_apply_eq (hG : G.IsTree) {f : G ≃g G}
    {c u v : V} (hc : f c = c) (hcyc : Equiv.Perm.SameCycle f.toEquiv u v) : ¬ G.Adj u v :=
  hG.isBipartite.not_adj_of_sameCycle_of_apply_eq hc (hG.connected c u) hcyc

/-- **A vertex whose degree is unique in a locally finite graph is fixed by every automorphism.** -/
theorem Iso.apply_eq_of_degree_unique [G.LocallyFinite] (f : G ≃g G) {c : V}
    (huniq : ∀ v : V, G.degree v = G.degree c → v = c) : f c = c :=
  huniq (f c) (f.degree_eq c)

/-- **On a locally finite tree with a vertex of unique degree, every automorphism orbit is an
independent set.** -/
theorem IsTree.not_adj_of_sameCycle_of_degree_unique [G.LocallyFinite] (hG : G.IsTree)
    {f : G ≃g G} {c u v : V} (huniq : ∀ w : V, G.degree w = G.degree c → w = c)
    (hcyc : Equiv.Perm.SameCycle f.toEquiv u v) : ¬ G.Adj u v :=
  hG.not_adj_of_sameCycle_of_apply_eq (f.apply_eq_of_degree_unique huniq) hcyc

/-! ## Automorphisms and reversal orbits of path graphs -/

/-- **An automorphism of `pathGraph n` fixing vertex `0` is the identity.** Once vertex `0` is
pinned, each subsequent vertex `k + 1` is forced inductively as the unique unused neighbour of `k`.
-/
theorem Iso.eq_refl_of_pathGraph_apply_zero {n : ℕ} (f : pathGraph n ≃g pathGraph n)
    (hn : 0 < n) (h0 : f ⟨0, hn⟩ = ⟨0, hn⟩) : f = Iso.refl := by
  have hfix : ∀ (k : ℕ) (hk : k < n), f ⟨k, hk⟩ = ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      rcases k with _ | k
      · exact h0
      · have hk' : k < n := by omega
        have hadj : (pathGraph n).Adj ⟨k, hk'⟩ ⟨k + 1, hk⟩ :=
          pathGraph_adj.mpr (Or.inl rfl)
        have hmap : (pathGraph n).Adj (f ⟨k, hk'⟩) (f ⟨k + 1, hk⟩) :=
          f.map_adj_iff.mpr hadj
        rw [ih k (Nat.lt_succ_self k) hk', pathGraph_adj] at hmap
        rcases hmap with hstep | hback
        · exact Fin.ext hstep.symm
        · simp only at hback
          rcases k with _ | j
          · omega
          · have hj : j < n := by omega
            have heq : f ⟨j + 1 + 1, hk⟩ = f ⟨j, hj⟩ := by
              rw [ih j (by omega) hj]
              exact Fin.ext (by simp only; omega)
            have hinj := Fin.mk.inj (f.injective heq)
            omega
  exact RelIso.ext fun ⟨k, hk⟩ ↦ hfix k hk

/-- **Every automorphism of `pathGraph n` is either the identity or the reversal
`TauCeti.pathGraphRevIso n`.** An interior vertex has two distinct neighbours in `pathGraph n`
whereas `0` has at most one, so `f` sends `0` either to `0` or to `n - 1`, and composing with
reversal reduces the second case to the first. -/
theorem Iso.eq_refl_or_eq_pathGraphRevIso {n : ℕ} (f : pathGraph n ≃g pathGraph n) :
    f = Iso.refl ∨ f = TauCeti.pathGraphRevIso n := by
  rcases le_or_gt n 1 with hn | hn
  · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
    exact Or.inl (RelIso.ext fun i ↦ Subsingleton.elim _ _)
  · have h0lt : 0 < n := by omega
    set x := f ⟨0, h0lt⟩ with hx
    -- Vertex `0` cannot map to an interior vertex `x` (`0 < x` and `x + 1 < n`), because `0` has
    -- only vertex `1` as a neighbour while `x` has both `x - 1` and `x + 1`.
    have h_end : (x : ℕ) = 0 ∨ (x : ℕ) = n - 1 := by
      by_contra hmid
      push Not at hmid
      have hx_pos : 0 < (x : ℕ) := by omega
      have hx_lt : (x : ℕ) + 1 < n := by have := x.isLt; omega
      set u : Fin n := ⟨(x : ℕ) - 1, by omega⟩
      set w : Fin n := ⟨(x : ℕ) + 1, hx_lt⟩
      have hu_adj : (pathGraph n).Adj ⟨0, h0lt⟩ (f.symm u) := by
        have : (pathGraph n).Adj x u :=
          pathGraph_adj.mpr (Or.inr (by simp only [u]; omega))
        simpa [hx] using f.symm.map_adj_iff.mpr this
      have hw_adj : (pathGraph n).Adj ⟨0, h0lt⟩ (f.symm w) := by
        have : (pathGraph n).Adj x w := pathGraph_adj.mpr (Or.inl rfl)
        simpa [hx] using f.symm.map_adj_iff.mpr this
      rw [pathGraph_adj] at hu_adj hw_adj
      simp only at hu_adj hw_adj
      have huw : f.symm u = f.symm w := Fin.ext (by omega)
      have := Fin.mk.inj (f.symm.injective huw)
      omega
    rcases h_end with hx0 | hxn
    · exact Or.inl (f.eq_refl_of_pathGraph_apply_zero h0lt (Fin.ext hx0))
    · right
      let g : pathGraph n ≃g pathGraph n := f.trans (TauCeti.pathGraphRevIso n)
      have hg0 : g ⟨0, h0lt⟩ = ⟨0, h0lt⟩ := by
        apply Fin.ext
        simp only [g, RelIso.trans_apply, TauCeti.pathGraphRevIso_apply, Fin.val_rev, ← hx]
        omega
      have hg := g.eq_refl_of_pathGraph_apply_zero h0lt hg0
      refine RelIso.ext fun i ↦ ?_
      have hi := congrArg (fun φ : pathGraph n ≃g pathGraph n ↦ φ i) hg
      simp only [g, RelIso.trans_apply, TauCeti.pathGraphRevIso_apply, RelIso.refl_apply] at hi
      simpa only [TauCeti.pathGraphRevIso_apply, Fin.rev_rev] using congrArg Fin.rev hi

/-- **A vertex `i` of `pathGraph n` is adjacent to its reversal `i.rev` exactly when `n` is even
and `i` is one of the two middle vertices `n / 2 - 1` or `n / 2`.** -/
@[simp]
theorem pathGraph_adj_rev_iff {n : ℕ} (i : Fin n) :
    (pathGraph n).Adj i i.rev ↔ 2 * (i : ℕ) + 2 = n ∨ 2 * (i : ℕ) = n := by
  rw [pathGraph_adj, Fin.val_rev]
  have := i.isLt
  omega

/-- **On an odd path graph, every orbit of the reversal permutation is an independent set.** -/
theorem not_pathGraph_adj_of_sameCycle_revPerm_of_odd {n : ℕ} (hn : Odd n) {i j : Fin n}
    (h : Fin.revPerm.SameCycle i j) : ¬ (pathGraph n).Adj i j := by
  have hrev : Function.Involutive (Fin.revPerm : Equiv.Perm (Fin n)) := Fin.rev_involutive
  rcases (hrev.sameCycle_iff i j).mp h with rfl | rfl
  · exact (pathGraph n).loopless.irrefl i
  · rw [adj_comm, Fin.revPerm_apply, pathGraph_adj_rev_iff]
    obtain ⟨k, rfl⟩ := hn
    omega

/-- **On an even path graph `pathGraph (2 * n)` (`1 ≤ n`), the middle pair `{n - 1, n}` is the
unique reversal orbit containing an edge.** -/
theorem sameCycle_revPerm_and_pathGraph_even_adj_iff {n : ℕ} (hn : 1 ≤ n)
    {i j : Fin (2 * n)} :
    Fin.revPerm.SameCycle i j ∧ (pathGraph (2 * n)).Adj i j ↔
      (i = ⟨n - 1, by omega⟩ ∧ j = ⟨n, by omega⟩) ∨
        (i = ⟨n, by omega⟩ ∧ j = ⟨n - 1, by omega⟩) := by
  have hrev : Function.Involutive (Fin.revPerm : Equiv.Perm (Fin (2 * n))) := Fin.rev_involutive
  constructor
  · rintro ⟨hcyc, hadj⟩
    rcases (hrev.sameCycle_iff i j).mp hcyc with rfl | rfl
    · exact absurd hadj ((pathGraph (2 * n)).loopless.irrefl i)
    · rw [adj_comm, Fin.revPerm_apply, pathGraph_adj_rev_iff] at hadj
      rcases hadj with hleft | hright
      · right
        have hj : (j : ℕ) = n - 1 := by omega
        refine ⟨Fin.ext ?_, Fin.ext hj⟩
        simp only [Fin.revPerm_apply, Fin.val_rev, hj]
        omega
      · left
        have hj : (j : ℕ) = n := by omega
        refine ⟨Fin.ext ?_, Fin.ext hj⟩
        simp only [Fin.revPerm_apply, Fin.val_rev, hj]
        omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨(hrev.sameCycle_iff _ _).mpr (Or.inr ?_),
        pathGraph_adj.mpr (Or.inl (by simp only; omega))⟩
      ext
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    · refine ⟨(hrev.sameCycle_iff _ _).mpr (Or.inr ?_),
        pathGraph_adj.mpr (Or.inr (by simp only; omega))⟩
      ext
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega

end SimpleGraph
