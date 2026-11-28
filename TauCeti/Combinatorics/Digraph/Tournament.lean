/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.Data.List.Chain

/-!
# Tournaments and their spanning paths

A tournament is a digraph with exactly one arc between any two distinct vertices and no loops
(J. W. Moon, *Topics on Tournaments*, 1968, §1). A spanning path of a digraph is a list of all its
vertices, without repetition, in which each entry has an arc to the next. A spanning cycle is a
cyclic permutation `σ` that moves every vertex and has an arc from each vertex `v` to `σ v`
(Moon, §4).

The main result is Rédei's theorem in its existence form: every tournament on a finite vertex
type has a spanning path (L. Rédei, 1934; Moon, §9). The proof inserts the vertices one at a time
into a path, and it uses only that any two distinct vertices are joined by an arc in at least one
direction, so it holds for every digraph with this property.

## Main definitions

* `Digraph.IsTournament`: the digraph has exactly one arc between any two distinct vertices.
* `Digraph.IsSpanningPath`: a list of vertices is a spanning path of the digraph.
* `Digraph.IsSpanningCycle`: a permutation of the vertices is a spanning cycle of the digraph.

## Main results

* `Digraph.exists_isSpanningPath`: a digraph on a finite vertex type in which any two distinct
  vertices are joined by an arc in at least one direction has a spanning path.
* `Digraph.IsTournament.exists_isSpanningPath`: every tournament on a finite vertex type has a
  spanning path.
* `Digraph.isTournament_lt`: the strict order of a linear order is a tournament.
* `Digraph.IsSpanningCycle.nontrivial`: a digraph with a spanning cycle has at least two vertices.
* `Digraph.isSpanningCycle_finRotate`: `finRotate` is a spanning cycle of the digraph of its arcs.
-/

public section

namespace Digraph

variable {W : Type*}

/-- A tournament is a digraph with exactly one arc between any two distinct vertices: no two
vertices have arcs in both directions, and any two distinct vertices have an arc in one direction.
In particular a tournament has no loops. -/
structure IsTournament (T : Digraph W) : Prop where
  /-- No two vertices of a tournament have arcs in both directions. -/
  asymm : ∀ ⦃u v⦄, T.Adj u v → ¬T.Adj v u
  /-- Any two distinct vertices of a tournament have an arc in one direction. -/
  adj_or_adj : ∀ ⦃u v⦄, u ≠ v → T.Adj u v ∨ T.Adj v u

/-- A spanning path of a digraph: a list of vertices without repetition that contains every vertex
and in which each entry has an arc to the next. -/
structure IsSpanningPath (D : Digraph W) (l : List W) : Prop where
  /-- A spanning path has no repeated vertex. -/
  nodup : l.Nodup
  /-- A spanning path contains every vertex. -/
  mem : ∀ v, v ∈ l
  /-- Each entry of a spanning path has an arc to the next. -/
  isChain : l.IsChain D.Adj

/-- A spanning cycle of a digraph: a cyclic permutation `σ` of the vertices that moves every vertex
and has an arc from each vertex `v` to `σ v`. -/
structure IsSpanningCycle (D : Digraph W) (σ : Equiv.Perm W) : Prop where
  /-- A spanning cycle is a cycle in the sense of `Equiv.Perm.IsCycle`. -/
  isCycle : σ.IsCycle
  /-- A spanning cycle moves every vertex. -/
  apply_ne : ∀ v, σ v ≠ v
  /-- A spanning cycle has an arc from each vertex to its image. -/
  adj : ∀ v, D.Adj v (σ v)

namespace IsTournament

variable {T : Digraph W}

/-- A tournament has no loops. -/
theorem not_adj_self (hT : T.IsTournament) (v : W) : ¬T.Adj v v :=
  fun h => hT.asymm h h

/-- The two endpoints of an arc of a tournament are distinct. -/
theorem ne_of_adj (hT : T.IsTournament) {u v : W} (h : T.Adj u v) : u ≠ v := by
  rintro rfl
  exact hT.not_adj_self u h

/-- Between two distinct vertices of a tournament there is an arc in one direction exactly when
there is none in the other. -/
theorem adj_iff_not_adj (hT : T.IsTournament) {u v : W} (h : u ≠ v) :
    T.Adj u v ↔ ¬T.Adj v u :=
  ⟨fun huv => hT.asymm huv, fun hvu => (hT.adj_or_adj h).resolve_right hvu⟩

end IsTournament

/-- The strict order of a linear order is a tournament. -/
theorem isTournament_lt [LinearOrder W] : ({ Adj := (· < ·) } : Digraph W).IsTournament where
  asymm _ _ := lt_asymm
  adj_or_adj _ _ := lt_or_gt_of_ne

/-- On an empty vertex type the empty list is a spanning path of every digraph. -/
theorem isSpanningPath_nil [IsEmpty W] (D : Digraph W) : D.IsSpanningPath [] where
  nodup := List.nodup_nil
  mem v := isEmptyElim v
  isChain := List.isChain_nil

/-- On a vertex type with at most one element, the list of any one vertex is a spanning path of
every digraph. -/
theorem isSpanningPath_singleton [Subsingleton W] (D : Digraph W) (v : W) :
    D.IsSpanningPath [v] where
  nodup := List.nodup_singleton v
  mem w := List.mem_singleton.2 (Subsingleton.elim w v)
  isChain := List.isChain_singleton v

/-- A spanning path of a digraph on a finite vertex type has one entry for each vertex. -/
theorem IsSpanningPath.length_eq [Fintype W] {D : Digraph W} {l : List W}
    (hl : D.IsSpanningPath l) : l.length = Fintype.card W := by
  classical
  rw [← List.toFinset_card_of_nodup hl.nodup,
    Finset.eq_univ_of_forall fun v => List.mem_toFinset.2 (hl.mem v), Finset.card_univ]

/-- A digraph with a spanning cycle has at least two vertices. -/
theorem IsSpanningCycle.nontrivial {D : Digraph W} {σ : Equiv.Perm W}
    (hσ : D.IsSpanningCycle σ) : Nontrivial W := by
  obtain ⟨v, hv, -⟩ := hσ.isCycle
  exact ⟨σ v, v, hv⟩

/-- The rotation `finRotate (n + 2)` of `Fin (n + 2)` is a spanning cycle of the digraph whose arcs
go from each `i` to `finRotate (n + 2) i`. -/
theorem isSpanningCycle_finRotate (n : ℕ) :
    ({ Adj := fun i j => j = finRotate (n + 2) i } : Digraph (Fin (n + 2))).IsSpanningCycle
      (finRotate (n + 2)) where
  isCycle := isCycle_finRotate
  apply_ne i := Equiv.Perm.mem_support.1 (by simp [support_finRotate])
  adj _ := rfl

/-- A digraph on a finite vertex type in which any two distinct vertices are joined by an arc in
at least one direction has a spanning path. -/
theorem exists_isSpanningPath [Finite W] {D : Digraph W}
    (h : ∀ ⦃u v⦄, u ≠ v → D.Adj u v ∨ D.Adj v u) : ∃ l, D.IsSpanningPath l := by
  have := Fintype.ofFinite W
  obtain ⟨l, hl, hcl⟩ := ((Finset.univ : Finset W).nodup_toList.imp_of_mem
    fun _ _ huv => h huv).exists_perm_isChain
  exact ⟨l, ⟨hl.nodup_iff.2 (Finset.nodup_toList _), fun v => by simp [hl.mem_iff], hcl⟩⟩

/-- Rédei's theorem, existence form: every tournament on a finite vertex type has a spanning
path. -/
theorem IsTournament.exists_isSpanningPath [Finite W] {T : Digraph W} (hT : T.IsTournament) :
    ∃ l, T.IsSpanningPath l :=
  Digraph.exists_isSpanningPath hT.adj_or_adj

end Digraph
