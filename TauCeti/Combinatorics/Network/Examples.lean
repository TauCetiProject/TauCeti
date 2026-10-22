/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import TauCeti.Combinatorics.Network.Acyclic
import TauCeti.Combinatorics.Network.Coefficients

/-!
# Examples of bounded assignments and flows

Take two vertices `false` and `true`, with one arrow for each ordered pair, including the two
loops, lower bound `-2` and upper bound `1` on every arrow. The integral assignment with value
`-1` on the arrow from `false` to `true` and zero elsewhere is a bounded `false`–`true` assignment
of negative value `-1`; conservation is vacuous because both vertices are terminals. Casting its
coefficients from `ℤ` to `ℝ` gives a real bounded assignment for the cast bounds, of value `-1`.

Take four vertices `s = 0`, `a = 1`, `b = 2` and `t = 3`, with one arrow for each ordered pair. The
unit flows along `s → a → b → t` and `s → b → a → t` add up to an `s`–`t` flow of value `2` that
these two paths decompose without any cycle, although its arrows of positive value contain the
cycle `a → b → a`. The unit flows along `s → a → t` and `s → b → t` add up to an acyclic flow of
the same value below it.
-/

namespace TauCeti

-- An integral bounded assignment with negative bounds and negative value, carried to `ℝ`.
example :
    let lo : Assignment (fun _ _ : Bool ↦ Unit) ℤ := fun _ _ _ ↦ -2
    let hi : Assignment (fun _ _ : Bool ↦ Unit) ℤ := fun _ _ _ ↦ 1
    let φ : ℤ →+o ℝ :=
      { toFun := Int.cast
        map_zero' := Int.cast_zero
        map_add' := Int.cast_add
        monotone' := Int.cast_mono }
    ∃ f : BoundedFlow lo hi false true, f.val = -1 ∧ (f.map φ).val = -1 ∧
      (f.map φ).toFun (x := false) (y := true) () = -1 := by
  intro lo hi φ
  refine ⟨⟨fun a b _ ↦ if a = false ∧ b = true then -1 else 0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro a b _
    simp only [lo]
    split_ifs <;> norm_num
  · intro a b _
    simp only [hi]
    split_ifs <;> norm_num
  · intro v hvs hvt
    cases v <;> simp_all
  · simp [BoundedFlow.val_def, excessAt_def]
  · simp [BoundedFlow.val_def, excessAt_def, φ]
  · simp [φ]

-- A flow with a cycle-free decomposition whose support contains a cycle, and an acyclic flow of
-- the same value below it.
example :
    let p₁ : ArrowWalk (fun _ _ : Fin 4 ↦ Unit) 0 3 :=
      (((ArrowWalk.nil 0).cons (x := 1) ()).cons (x := 2) ()).cons (x := 3) ()
    let p₂ : ArrowWalk (fun _ _ : Fin 4 ↦ Unit) 0 3 :=
      (((ArrowWalk.nil 0).cons (x := 2) ()).cons (x := 1) ()).cons (x := 3) ()
    let q₁ : ArrowWalk (fun _ _ : Fin 4 ↦ Unit) 0 3 :=
      ((ArrowWalk.nil 0).cons (x := 1) ()).cons (x := 3) ()
    let q₂ : ArrowWalk (fun _ _ : Fin 4 ↦ Unit) 0 3 :=
      ((ArrowWalk.nil 0).cons (x := 2) ()).cons (x := 3) ()
    let f : Assignment (fun _ _ : Fin 4 ↦ Unit) ℤ := walkAssignment p₁ 1 + walkAssignment p₂ 1
    let g : Assignment (fun _ _ : Fin 4 ↦ Unit) ℤ := walkAssignment q₁ 1 + walkAssignment q₂ 1
    ∃ (F G : Flow f 0 3) (D : PathCycleDecomposition f), F.toFun = f ∧ G.toFun = g ∧
      F.val = 2 ∧ G.val = 2 ∧ D.cycles = [] ∧ ¬f.IsAcyclic ∧ g.IsAcyclic := by
  intro p₁ p₂ q₁ q₂ f g
  have hf₀ : 0 ≤ f := add_nonneg (walkAssignment_nonneg _ zero_le_one)
    (walkAssignment_nonneg _ zero_le_one)
  have hgf : g ≤ f := by
    intro x y e
    fin_cases x <;> fin_cases y <;>
      simp [f, g, p₁, p₂, q₁, q₂, Assignment.single_apply]
  let F : Flow f 0 3 :=
    { toFun := f
      mem_Icc := ⟨hf₀, le_rfl⟩
      conserve v hv₀ hv₃ := by simp [f, excessAt_add, hv₀, hv₃]
      excessAt_sink_nonneg := by simp [f, excessAt_add] }
  let G : Flow f 0 3 :=
    { toFun := g
      mem_Icc := ⟨add_nonneg (walkAssignment_nonneg _ zero_le_one)
        (walkAssignment_nonneg _ zero_le_one), hgf⟩
      conserve v hv₀ hv₃ := by simp [g, excessAt_add, hv₀, hv₃]
      excessAt_sink_nonneg := by simp [g, excessAt_add] }
  let D : PathCycleDecomposition f :=
    { paths := [⟨0, 3, p₁, 1⟩, ⟨0, 3, p₂, 1⟩]
      cycles := []
      isPath_walk := by simp [ArrowWalk.isPath_def, p₁, p₂, Quiver.Path.vertices_cons]
      isCycle_walk := by simp
      weight_pos_of_mem_paths := by simp
      weight_pos_of_mem_cycles := by simp
      excessAt_source_neg := by simp [f, excessAt_add]
      excessAt_target_pos := by simp [f, excessAt_add]
      sum_paths_add_sum_cycles := by simp [f, WeightedWalk.assignment_def] }
  refine ⟨F, G, D, rfl, rfl, ?_, ?_, rfl, ?_, ?_⟩
  · simp [F, BoundedFlow.val_def, f, excessAt_add]
  · simp [G, BoundedFlow.val_def, g, excessAt_add]
  · -- The arrows `a → b` and `b → a` both carry one unit.
    rw [Assignment.isAcyclic_iff_forall_not_transGen]
    push Not
    refine ⟨1, .tail (.single ⟨(), ?_⟩) (c := 1) (b := 2) ⟨(), ?_⟩⟩ <;>
      simp [f, p₁, p₂, Assignment.single_apply]
  · -- Every arrow of positive value strictly raises the rank `![0, 1, 1, 2]`.
    let r : Fin 4 → ℕ := ![0, 1, 1, 2]
    have step (x y : Fin 4) (h : ∃ e, 0 < g (x := x) (y := y) e) : r x < r y := by
      fin_cases x <;> fin_cases y <;> simp_all [r, g, q₁, q₂, Assignment.single_apply]
    rw [Assignment.isAcyclic_iff_forall_not_transGen]
    intro v h
    suffices ∀ {x y}, Relation.TransGen (fun v w ↦ ∃ e, 0 < g (x := v) (y := w) e) x y →
        r x < r y from lt_irrefl _ (this h)
    intro x y hxy
    induction hxy with
    | single h => exact step _ _ h
    | tail _ h ih => exact ih.trans (step _ _ h)

end TauCeti
