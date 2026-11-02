/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Scott.Rank
public import TauCeti.ModelTheory.BackAndForth.Graph
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A rigid finite graph and its Scott rank

This file gives a concrete rigid graph on six vertices. It consists of a triangle on vertices
`0`, `1`, `2`, with paths `0 - 3 - 5` and `1 - 4` attached. The two attachment paths distinguish
`0` from `1`; the remaining vertices are then distinguished by their incidences. Consequently
every automorphism is the identity.

The back-and-forth analysis is also explicit. All vertices agree at level one, because every
vertex has a neighbour and a distinct non-neighbour. At level two the six vertices lie in distinct
classes. Reindexing a tuple to each of its coordinates then shows that every tuple is orbit-stable
at level two. Thus every vertex has orbit rank two and the graph has internal Scott rank three.

## Main results

* `TauCeti.rigidSixGraph_iso_eq_refl`: every automorphism of the graph is the identity.
* `TauCeti.orbitRank_rigidSixGraph`: every vertex has orbit rank two.
* `TauCeti.internalScottRank_rigidSixGraph`: the graph has internal Scott rank three.
-/

public section

namespace TauCeti

/-- A rigid graph on six vertices: a triangle with paths of lengths two and one attached at
different vertices. -/
def rigidSixGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun i j =>
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
    (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 5)

/-- The adjacency relation of `rigidSixGraph`, listed as its twelve oriented edges. -/
@[simp]
theorem rigidSixGraph_adj (i j : Fin 6) : rigidSixGraph.Adj i j ↔
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
    (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1) ∨
    (i = 3 ∧ j = 5) ∨ (i = 5 ∧ j = 3) := by
  fin_cases i <;> fin_cases j <;> simp [rigidSixGraph]

end TauCeti

namespace TauCeti

open FirstOrder FirstOrder.Language Fin
open scoped Ordinal

private local instance : Language.graph.Structure (Fin 6) := rigidSixGraph.structure

private local instance : DecidableRel rigidSixGraph.Adj := fun i j =>
  decidable_of_iff _ (rigidSixGraph_adj i j).symm

/-- At level one, all vertices of `rigidSixGraph` are back-and-forth equivalent. -/
private theorem bfEquiv_one_rigidSixGraph (v w : Fin 6) :
    BFEquiv (L := Language.graph) (1 : Ordinal.{o}) 1 (fun _ => v) (fun _ => w) := by
  rw [BFEquiv.one]
  simp only [SimpleGraph.sameAtomicType_iff]
  revert v w
  decide

/-- Distinct vertices can be separated by one move on one side whose resulting pairs fail
level-one back-and-forth equivalence. -/
private theorem exists_separating_move_rigidSixGraph (v w : Fin 6) : v ≠ w →
    (∃ x, ∀ y, ¬ BFEquiv (L := Language.graph) (1 : Ordinal.{o}) 2
      (snoc (fun _ : Fin 1 => v) x) (snoc (fun _ : Fin 1 => w) y)) ∨
    (∃ y, ∀ x, ¬ BFEquiv (L := Language.graph) (1 : Ordinal.{o}) 2
      (snoc (fun _ : Fin 1 => v) x) (snoc (fun _ : Fin 1 => w) y)) := by
  simp only [BFEquiv.one, SimpleGraph.sameAtomicType_iff]
  fin_cases v <;> fin_cases w <;> decide

/-- Level two distinguishes all vertices of `rigidSixGraph`. -/
private theorem bfEquiv_two_rigidSixGraph_iff (v w : Fin 6) :
    BFEquiv (L := Language.graph) (2 : Ordinal.{o}) 1 (fun _ => v) (fun _ => w) ↔ v = w := by
  refine ⟨fun h => ?_, fun h => h ▸ BFEquiv.refl 2 (fun _ : Fin 1 => v)⟩
  by_contra hvw
  rw [show (2 : Ordinal.{o}) = 1 + 1 by norm_num, BFEquiv.add_one] at h
  rcases exists_separating_move_rigidSixGraph v w hvw with ⟨x, hx⟩ | ⟨y, hy⟩
  · obtain ⟨y, hxy⟩ := h.2.1 x
    exact hx y hxy
  · obtain ⟨x, hxy⟩ := h.2.2 y
    exact hy x hxy

/-- Every automorphism of `rigidSixGraph` is the identity. -/
theorem rigidSixGraph_iso_eq_refl
    (e : rigidSixGraph ≃g rigidSixGraph) :
    e = SimpleGraph.Iso.refl := by
  apply RelIso.ext
  intro v
  have hb := e.toLanguageEquiv.bfEquiv (2 : Ordinal.{0}) (fun _ : Fin 1 => v)
  apply Eq.symm
  apply (bfEquiv_two_rigidSixGraph_iff v (e v)).mp
  simpa only [Function.comp_def, SimpleGraph.Iso.toLanguageEquiv_apply] using hb

/-- Every tuple of `rigidSixGraph` is orbit-stable at level two. -/
private theorem two_mem_orbitStable_rigidSixGraph {n : ℕ} (a : Fin n → Fin 6) :
    (2 : Ordinal) ∈ orbitStable (L := Language.graph) a := by
  rw [mem_orbitStable_iff]
  intro b h β
  have hab : a = b := by
    funext i
    exact (bfEquiv_two_rigidSixGraph_iff (a i) (b i)).mp
      (h.comp (fun _ : Fin 1 => i))
  subst b
  exact BFEquiv.refl β a

/-- Every vertex of `rigidSixGraph` has orbit rank two. -/
theorem orbitRank_rigidSixGraph (v : Fin 6) :
    letI := rigidSixGraph.structure
    orbitRank (L := Language.graph) (fun _ : Fin 1 => v) = 2 := by
  refine le_antisymm (orbitRank_le _ (two_mem_orbitStable_rigidSixGraph _)) ?_
  rw [← one_add_one_eq_two, Order.add_one_le_iff, lt_iff_not_ge, orbitRank_le_iff,
    mem_orbitStable_iff]
  intro h
  obtain ⟨w, hw⟩ := exists_ne v
  exact hw ((bfEquiv_two_rigidSixGraph_iff v w).mp
    (h (fun _ : Fin 1 => w) (bfEquiv_one_rigidSixGraph v w) 2)).symm

/-- The internal Scott rank of `rigidSixGraph` is three. -/
theorem internalScottRank_rigidSixGraph :
    letI := rigidSixGraph.structure
    internalScottRank (L := Language.graph) (Fin 6) = 3 := by
  rw [show (3 : Ordinal) = 2 + 1 by norm_num]
  exact internalScottRank_eq_add_one_of_mem_orbitStable_of_orbitRank_eq
    (fun _ a => two_mem_orbitStable_rigidSixGraph a)
    (orbitRank_rigidSixGraph 0)

end TauCeti
