/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Chordal.Simplicial

import Mathlib.Data.Fintype.Lattice
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import TauCeti.Combinatorics.SimpleGraph.CycleGraph

/-!
# Perfect elimination orderings

An ordering of the vertices of a simple graph is a bijection `σ : V ≃ Fin n`, and `w` comes after
`v` when `σ v < σ w`. It is a *perfect elimination ordering*
(`SimpleGraph.IsPerfectEliminationOrder`) when the neighbours of every vertex that come after it
are pairwise adjacent: deleting the vertices one at a time in the order `σ`, each vertex is
simplicial in the graph that remains when it is deleted. In particular the first vertex is
simplicial.

The main result is the theorem of Fulkerson and Gross that a finite graph is chordal if and only if
it has a perfect elimination ordering
(`SimpleGraph.isChordal_iff_exists_isPerfectEliminationOrder`).

* A graph with a perfect elimination ordering is chordal: in an induced cycle on at least four
  vertices, the two cycle neighbours of the vertex of the cycle that comes first both come after
  it, so they are adjacent, and that is a chord.
* A finite chordal graph has a perfect elimination ordering, by induction on the number of
  vertices: by Dirac's theorem it has a simplicial vertex `v`, which is put first, followed by a
  perfect elimination ordering of the chordal graph induced on the other vertices.

Perfect elimination orderings are what colours a chordal graph with as many colours as its clique
number: colouring from the last vertex to the first, the neighbours of a vertex coloured before it
are its later neighbours, which together with the vertex form a clique
(`SimpleGraph.IsPerfectEliminationOrder.isClique_insert`).

## Main definitions

* `SimpleGraph.IsPerfectEliminationOrder G σ`: the neighbours of every vertex that come after it in
  the ordering `σ` are pairwise adjacent.

## Main results

* `SimpleGraph.IsPerfectEliminationOrder.isSimplicial_of_forall_le`: the first vertex of a perfect
  elimination ordering is simplicial.
* `SimpleGraph.IsPerfectEliminationOrder.isChordal`: a graph with a perfect elimination ordering is
  chordal.
* `SimpleGraph.IsChordal.exists_isPerfectEliminationOrder`: a finite chordal graph has a perfect
  elimination ordering.
* `SimpleGraph.isChordal_iff_exists_isPerfectEliminationOrder`: **the theorem of Fulkerson and
  Gross**, a finite graph is chordal if and only if it has a perfect elimination ordering.

## References

* D. R. Fulkerson and O. A. Gross, *Incidence matrices and interval graphs*, Pacific J. Math. 15
  (1965).
* L. Vandenberghe and M. S. Andersen, *Chordal Graphs and Semidefinite Optimization*, Foundations
  and Trends in Optimization 1 (4), 2014, Sections 4.1–4.2, Theorem 4.1.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} {σ : V ≃ Fin n}

/-- An ordering `σ` of the vertices of `G` is a *perfect elimination ordering* when, for every
vertex `v`, the neighbours of `v` that come after it in `σ` form a clique. -/
def IsPerfectEliminationOrder (G : SimpleGraph V) (σ : V ≃ Fin n) : Prop :=
  ∀ v, G.IsClique {w | G.Adj v w ∧ σ v < σ w}

theorem isPerfectEliminationOrder_def :
    G.IsPerfectEliminationOrder σ ↔ ∀ v, G.IsClique {w | G.Adj v w ∧ σ v < σ w} :=
  Iff.rfl

/-- An ordering is a perfect elimination ordering exactly when any two distinct neighbours of a
vertex that both come after it are adjacent. -/
theorem isPerfectEliminationOrder_iff :
    G.IsPerfectEliminationOrder σ ↔ ∀ ⦃v x y⦄, G.Adj v x → G.Adj v y → σ v < σ x → σ v < σ y →
      x ≠ y → G.Adj x y :=
  ⟨fun h _ _ _ hx hy hvx hvy hxy ↦ h _ ⟨hx, hvx⟩ ⟨hy, hvy⟩ hxy,
    fun h _ _ hx _ hy hxy ↦ h hx.1 hy.1 hx.2 hy.2 hxy⟩

/-- In a perfect elimination ordering, two distinct neighbours of a vertex that both come after it
are adjacent. -/
theorem IsPerfectEliminationOrder.adj (hσ : G.IsPerfectEliminationOrder σ) {v x y : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hvx : σ v < σ x) (hvy : σ v < σ y) (hxy : x ≠ y) :
    G.Adj x y :=
  isPerfectEliminationOrder_iff.1 hσ hx hy hvx hvy hxy

/-- In a perfect elimination ordering, a vertex together with its neighbours that come after it
forms a clique. -/
theorem IsPerfectEliminationOrder.isClique_insert (hσ : G.IsPerfectEliminationOrder σ) (v : V) :
    G.IsClique (insert v {w | G.Adj v w ∧ σ v < σ w}) :=
  (hσ v).insert fun _ hw _ ↦ hw.1

/-- The first vertex of a perfect elimination ordering is simplicial. -/
theorem IsPerfectEliminationOrder.isSimplicial_of_forall_le (hσ : G.IsPerfectEliminationOrder σ)
    {v : V} (hv : ∀ w, σ v ≤ σ w) : G.IsSimplicial v := by
  rw [isSimplicial_def]
  refine (hσ v).subset fun w hw ↦ ?_
  exact ⟨hw, (hv w).lt_of_ne (σ.injective.ne (G.ne_of_adj hw))⟩

/-- Every ordering of the vertices of a complete graph is a perfect elimination ordering. -/
@[simp]
theorem isPerfectEliminationOrder_top (σ : V ≃ Fin n) :
    (⊤ : SimpleGraph V).IsPerfectEliminationOrder σ :=
  fun _ ↦ IsClique.top _

/-- **A graph with a perfect elimination ordering is chordal.** -/
theorem IsPerfectEliminationOrder.isChordal (hσ : G.IsPerfectEliminationOrder σ) : G.IsChordal := by
  rw [isChordal_def]
  rintro m hm ⟨f⟩
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by lia⟩
  -- the vertex of the cycle that comes first in `σ`, rotated to position `1`
  obtain ⟨i, hi⟩ := Finite.exists_min fun j ↦ σ (f j)
  let g := f.comp (TauCeti.cycleGraphAddRightIso (i - ⟨1, by lia⟩)).toEmbedding
  have hg (j : Fin (m + 4)) : g j = f (j + (i - ⟨1, by lia⟩)) := by
    simp [g, TauCeti.cycleGraphAddRightIso_apply]
  have hmin (j : Fin (m + 4)) : σ (g ⟨1, by lia⟩) ≤ σ (g j) := by
    rw [hg, hg, add_sub_cancel]
    exact hi _
  have hadj {j k : ℕ} (hj : j < m + 4) (hk : k < m + 4) :
      G.Adj (g ⟨j, hj⟩) (g ⟨k, hk⟩) ↔
        k = j + 1 ∨ j = k + 1 ∨ (j = 0 ∧ k = m + 3) ∨ (k = 0 ∧ j = m + 3) := by
    rw [g.map_adj_iff, TauCeti.cycleGraph_adj_iff_val (by lia)]
    lia
  -- the vertices at positions `0` and `2` come after the one at position `1`, so they are adjacent
  have hlt {j : ℕ} (hj : j < m + 4) (hj1 : j ≠ 1) : σ (g ⟨1, by lia⟩) < σ (g ⟨j, hj⟩) :=
    (hmin _).lt_of_ne (σ.injective.ne (g.injective.ne (Fin.ne_of_val_ne (Ne.symm hj1))))
  have := (hadj (j := 0) (k := 2) (by lia) (by lia)).1
    (hσ.adj ((hadj _ _).2 (by lia)) ((hadj _ _).2 (by lia)) (hlt _ (by lia)) (hlt _ (by lia))
      (g.injective.ne (Fin.ne_of_val_ne (by lia))))
  lia

/-- A simplicial vertex `v` of `G` put before a perfect elimination ordering of the graph induced on
the other vertices gives a perfect elimination ordering of `G`. -/
private theorem IsSimplicial.exists_isPerfectEliminationOrder {v : V} (hv : G.IsSimplicial v)
    {m : ℕ} {τ : ({v}ᶜ : Set V) ≃ Fin m}
    (hτ : (G.induce ({v}ᶜ : Set V)).IsPerfectEliminationOrder τ) :
    ∃ σ : V ≃ Fin (m + 1), G.IsPerfectEliminationOrder σ := by
  classical
  let σ : V ≃ Fin (m + 1) := (Equiv.optionSubtypeNe v).symm.trans <|
    (Equiv.optionCongr ((Equiv.subtypeEquivRight fun _ ↦ Set.mem_compl_singleton_iff.symm).trans
      τ)).trans (finSuccEquiv m).symm
  have hσv : σ v = 0 := by simp [σ]
  have hσ {w : V} (hw : w ∈ ({v}ᶜ : Set V)) : σ w = (τ ⟨w, hw⟩).succ := by
    simp [σ, Equiv.optionSubtypeNe_symm_of_ne (Set.mem_compl_singleton_iff.1 hw),
      Equiv.subtypeEquivRight_apply]
  refine ⟨σ, fun u ↦ ?_⟩
  by_cases hu : u = v
  · subst hu
    exact (isSimplicial_def.1 hv).subset fun w hw ↦ hw.1
  -- the later neighbours of `u ≠ v` are not `v`, which comes first, so they come after `u` in `τ`
  have hu' : u ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.2 hu
  have hlater {w : V} (hw : σ u < σ w) : w ∈ ({v}ᶜ : Set V) :=
    Set.mem_compl_singleton_iff.2 fun h ↦ (Fin.zero_le _).not_gt (hσv ▸ h ▸ hw)
  intro x ⟨hux, hx⟩ y ⟨huy, hy⟩ hxy
  have hx' := hlater hx
  have hy' := hlater hy
  rw [hσ hu', hσ hx', Fin.succ_lt_succ_iff] at hx
  rw [hσ hu', hσ hy', Fin.succ_lt_succ_iff] at hy
  exact induce_adj.1 (hτ.adj (v := ⟨u, hu'⟩) (x := ⟨x, hx'⟩) (y := ⟨y, hy'⟩) (induce_adj.2 hux)
    (induce_adj.2 huy) hx hy (Subtype.coe_ne_coe.1 hxy))

/-- **A finite chordal graph has a perfect elimination ordering.** -/
theorem IsChordal.exists_isPerfectEliminationOrder [Finite V] (hG : G.IsChordal) :
    ∃ (n : ℕ) (σ : V ≃ Fin n), G.IsPerfectEliminationOrder σ := by
  induction hn : Nat.card V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  cases isEmpty_or_nonempty V
  · exact ⟨0, Equiv.equivOfIsEmpty V (Fin 0), fun v ↦ isEmptyElim v⟩
  obtain ⟨v, hv⟩ := hG.exists_isSimplicial
  obtain ⟨m, τ, hτ⟩ := ih _ (hn ▸ Finite.card_subtype_lt (Set.notMem_compl_iff.2 rfl))
    (hG.induce ({v}ᶜ : Set V)) rfl
  obtain ⟨σ, hσ⟩ := hv.exists_isPerfectEliminationOrder hτ
  exact ⟨m + 1, σ, hσ⟩

/-- **The theorem of Fulkerson and Gross.** A finite graph is chordal if and only if it has a
perfect elimination ordering. -/
theorem isChordal_iff_exists_isPerfectEliminationOrder [Finite V] :
    G.IsChordal ↔ ∃ (n : ℕ) (σ : V ≃ Fin n), G.IsPerfectEliminationOrder σ :=
  ⟨IsChordal.exists_isPerfectEliminationOrder, fun ⟨_, _, hσ⟩ ↦ hσ.isChordal⟩

end SimpleGraph
