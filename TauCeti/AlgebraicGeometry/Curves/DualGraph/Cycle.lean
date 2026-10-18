/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# The dual graph of a cycle of rational curves

For `r ≥ 1`, glue `r` smooth rational curves in a ring, each one meeting the next in a node and
the last meeting the first. The dual graph of the resulting curve is `TauCeti.DualGraph.cycle r`:
its vertices and edges are both indexed by `ZMod r`, and the edge `e` joins the vertices `e` and
`e + 1`. For `r = 1` it is the dual graph of the irreducible rational curve with one node, whose
single edge is a loop. These are the configurations of Kodaira type `Iᵣ`.

Every vertex has genus zero and valence two, so the graph has arithmetic genus one and every
log-canonical degree vanishes: the cycle is semistable but not stable, the standard example
separating the two notions.
-/

public section

namespace TauCeti

namespace DualGraph

open Finset

variable (r : ℕ) [NeZero r]

/-- The dual graph of a cycle of `r` smooth rational curves, the edge `e` joining the vertices `e`
and `e + 1` of `ZMod r`; for `r = 1` its single edge is a loop. -/
abbrev cycle : DualGraph.{0, 0} Empty where
  Vertex := ZMod r
  Edge := ZMod r
  endpoint e i := if i = 0 then e else e + 1
  genus _ := 0
  marking := Empty.elim
  connected v w := by
    -- Walk from `v` along the edges `v, v + 1, …` until reaching `w = v + (w - v)`.
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, w = v + (k : ZMod r) := ⟨(w - v).val, by simp⟩
    induction k with
    | zero =>
      -- after rewriting, `rw` closes the goal `ReflTransGen _ v v` by reflexivity
      rw [Nat.cast_zero, add_zero]
    | succ k ih =>
      rw [Nat.cast_add_one, ← add_assoc]
      exact ih.tail ⟨v + k, Or.inl ⟨by simp, by simp⟩⟩

variable {r}

/-- Every vertex of a cycle has valence two: it carries one branch of the edge before it and one
of the edge after it, or both branches of the loop when `r = 1`. -/
@[simp]
theorem valence_cycle (v : ZMod r) : (cycle r).valence v = 2 := by
  rw [valence_def, card_eq_two]
  refine ⟨(v, 0), (v - 1, 1), by simp, ?_⟩
  ext ⟨e, i⟩
  fin_cases i <;> simp [eq_sub_iff_add_eq]

/-- A cycle of rational curves has arithmetic genus one. -/
@[simp]
theorem arithmeticGenus_cycle : (cycle r).arithmeticGenus = 1 := by
  have h := (cycle r).arithmeticGenus_add_card_vertex
  simp only [sum_const_zero, zero_add] at h
  have hcard : Fintype.card (cycle r).Vertex = Fintype.card (cycle r).Edge := rfl
  omega

/-- Every vertex of a cycle has log-canonical degree zero. -/
@[simp]
theorem logCanonicalDegree_cycle (v : ZMod r) : (cycle r).logCanonicalDegree v = 0 := by
  simp [logCanonicalDegree_def, valence_cycle]

/-- A cycle of rational curves is semistable. -/
@[simp]
theorem isSemistable_cycle : (cycle r).IsSemistable :=
  (cycle r).isSemistable_iff.mpr fun v ↦ (logCanonicalDegree_cycle v).ge

/-- A cycle of rational curves is not stable. -/
@[simp]
theorem not_isStable_cycle : ¬ (cycle r).IsStable :=
  fun h ↦ ((cycle r).isStable_iff.mp h 0).ne' (logCanonicalDegree_cycle 0)

end DualGraph

end TauCeti
