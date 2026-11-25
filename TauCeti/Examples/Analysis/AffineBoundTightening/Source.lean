/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.AffineBoundTightening.Source
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checks for bounded original-coordinate bound tightening

These checks cover initialization with an inconsistent affine row, empty coordinate
families, signed and zero coefficients, and a bounded original model with effective
nonlinear and integer restrictions. The model minimizes `(x₀ - 1)² + x₁²` subject to
`x₀ + x₁ ≤ 2`, `1 ≤ x₀² + x₁²`, and integer `x₀`, with initial bounds `[0, 2]²`.
The point `(1, 0)` attains objective value zero and remains a minimizer at the actual
endpoint limit. No LP feasibility result is used, and no general attainment assertion
is made.
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening.SourceExamples

noncomputable section

/-- The affine row `x₀ + x₁`. -/
def sumMatrix : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]

/-- The initial joint box for `x₀ + x₁ ≤ 2` on `[0, 2]²`. -/
def initial : Raw 2 1 := sourceInitial sumMatrix ![2] ![0, 0] ![2, 2]

/-- The nonlinear restriction `1 ≤ x₀² + x₁²`. -/
def nonlinearRestriction : Set (Fin 2 → ℝ) := {x | 1 ≤ x 0 ^ 2 + x 1 ^ 2}

/-- The original model retains the nonlinear restriction and integrality of `x₀`. -/
def feasible : Set (Fin 2 → ℝ) := sourceSet sumMatrix ![2] nonlinearRestriction {0}

/-- The unchanged original objective has a zero-value minimizer at `(1, 0)`. -/
def objective (x : Fin 2 → ℝ) : ℝ := (x 0 - 1) ^ 2 + x 1 ^ 2

/-- The row interval for `x₀ + x₁ ≤ 2` on `[0, 2]²` initializes to `[0, 2]`. -/
theorem initial_row : initial.1 (.inr 0) = 0 ∧ initial.2 (.inr 0) = 2 := by
  constructor
  · simp only [initial, sourceInitial_fst_inr, imageLo_def, Fin.sum_univ_two]
    rw [zLo_of_nonneg (A := sumMatrix) (i := 0) (j := 0) (by norm_num [sumMatrix]),
      zLo_of_nonneg (A := sumMatrix) (i := 0) (j := 1) (by norm_num [sumMatrix])]
    norm_num [sumMatrix]
  · simp [initial]

/-- Initialization can be ordered while no affine graph point is enclosed. -/
theorem ordered_initial_without_graph :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![1]
    let q := sourceInitial A ![0] ![1] ![1]
    q.1 ≤ q.2 ∧ q.1 (.inr 0) = 0 ∧ q.2 (.inr 0) = 0 ∧
      ¬ ∃ x, graph A x ∈ Icc q.1 q.2 := by
  intro A q
  have hlo : q.1 (.inr 0) = 0 := by
    simp only [q, sourceInitial_fst_inr, imageLo_def, Fin.sum_univ_one]
    rw [zLo_of_nonneg (A := A) (i := 0) (j := 0) (by norm_num [A])]
    norm_num [A]
  refine ⟨sourceInitial_fst_le_snd A ![0] le_rfl, hlo,
    by simp [q], ?_⟩
  rintro ⟨x, hx⟩
  have hx' := mem_Icc_sourceInitial_graph_iff.mp hx
  have hl := hx'.1.1 0
  have hr := hx'.2 0
  norm_num [A, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ] at hl hr
  linarith

/-- With no affine rows, graph membership in the initialization is just variable-box membership. -/
theorem no_rows_initial_graph_iff {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℝ)
    (r : Fin 0 → ℝ) (l u x : Fin n → ℝ) :
    graph A x ∈ Icc (sourceInitial A r l u).1 (sourceInitial A r l u).2 ↔ x ∈ Icc l u := by
  constructor
  · intro hx
    exact (mem_Icc_sourceInitial_graph_iff.mp hx).1
  · intro hx
    exact mem_Icc_sourceInitial_graph_iff.mpr ⟨hx, fun i => Fin.elim0 i⟩

/-- Removing affine rows leaves the extra restriction and integrality condition intact. -/
theorem no_rows_sourceSet_iff {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℝ)
    (r : Fin 0 → ℝ) (extra : Set (Fin n → ℝ)) (integers : Finset (Fin n)) (x : Fin n → ℝ) :
    x ∈ sourceSet A r extra integers ↔
      x ∈ extra ∧ ∀ j ∈ integers, ∃ z : ℤ, x j = (z : ℝ) := by
  rw [mem_sourceSet]
  constructor
  · intro hx
    exact ⟨hx.2.1, hx.2.2⟩
  · rintro ⟨he, hi⟩
    exact ⟨fun i => Fin.elim0 i, he, hi⟩

/-- With no variables, initialization is ordered and its enclosed graph condition is `0 ≤ r`. -/
theorem no_variables_initial {m : ℕ} (A : Matrix (Fin m) (Fin 0) ℝ)
    (r : Fin m → ℝ) (l u x : Fin 0 → ℝ) :
    (sourceInitial A r l u).1 ≤ (sourceInitial A r l u).2 ∧
      (graph A x ∈ Icc (sourceInitial A r l u).1 (sourceInitial A r l u).2 ↔
        ∀ i, 0 ≤ r i) := by
  refine ⟨sourceInitial_fst_le_snd A r (fun j => Fin.elim0 j), ?_⟩
  rw [mem_Icc_sourceInitial_graph_iff]
  simp [mem_Icc, Pi.le_def]

/-- At zero variables and rows the initialized graph survives every actual public iterate. -/
theorem zero_dimensions (A : Matrix (Fin 0) (Fin 0) ℝ) (r : Fin 0 → ℝ)
    (l u x : Fin 0 → ℝ) :
    (∀ k, (publicRun A (sourceInitial A r l u) k : Set (Coord 0 0 → ℝ)).Nonempty) ∧
      variableBox (endpointLimit A (sourceInitial A r l u)) = univ := by
  have hg : graph A x ∈ Icc (sourceInitial A r l u).1 (sourceInitial A r l u).2 :=
    mem_Icc_sourceInitial_graph_iff.mpr
      ⟨⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩, fun i => Fin.elim0 i⟩
  refine ⟨coe_publicRun_nonempty_of_graph hg, ?_⟩
  apply Set.eq_univ_of_forall
  intro _
  exact mem_variableBox.mpr fun j => Fin.elim0 j

/-- Negative and zero coefficients and a negative row cap retain their signed initialization. -/
theorem signed_initialization :
    let A : Matrix (Fin 1) (Fin 2) ℝ := !![-2, 0]
    let q := sourceInitial A ![-1] ![1, 2] ![3, 4]
    q.1 (.inr 0) = -6 ∧ q.2 (.inr 0) = -1 ∧ graph A ![1, 2] ∈ Icc q.1 q.2 := by
  intro A q
  have hlo : q.1 (.inr 0) = -6 := by
    simp only [q, sourceInitial_fst_inr, imageLo_def, Fin.sum_univ_two]
    rw [zLo_of_nonpos (A := A) (i := 0) (j := 0) (by norm_num [A]),
      zLo_of_zero (A := A) (i := 0) (j := 1) (by norm_num [A])]
    norm_num [A]
  refine ⟨hlo, by simp [q], ?_⟩
  apply mem_Icc_sourceInitial_graph_iff.mpr
  constructor
  · constructor <;> intro j <;> fin_cases j <;> norm_num
  · intro i
    fin_cases i
    norm_num [A, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]

/-- An empty extra set makes the original feasible set empty, with any affine or integer data. -/
theorem empty_extra {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (integers : Finset (Fin n)) : sourceSet A r ∅ integers = ∅ := by
  ext x
  simp

/-- With no designated integer coordinates the affine and extra restrictions still remain. -/
theorem empty_integers {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (extra : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    x ∈ sourceSet A r extra ∅ ↔ A.mulVec x ≤ r ∧ x ∈ extra := by
  simp

/-- The point `(1, 0)` satisfies every original restriction. -/
theorem optimum_feasible : ![1, 0] ∈ feasible := by
  unfold feasible
  rw [mem_sourceSet]
  refine ⟨?_, by norm_num [nonlinearRestriction], ?_⟩
  · intro i
    fin_cases i
    norm_num [sumMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]
  · intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    exact ⟨1, by norm_num⟩

/-- The point `(1, 0)` lies in the initial variable box. -/
theorem optimum_in_initial_box : ![1, 0] ∈ Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] := by
  constructor <;> intro j <;> fin_cases j <;> norm_num

/-- A concrete feasible graph point proves nonemptiness of all actual public iterates. -/
theorem original_nonempty_run (k : ℕ) :
    (publicRun sumMatrix initial k : Set (Coord 2 1 → ℝ)).Nonempty := by
  apply coe_publicRun_nonempty_of_graph (x := ![1, 0])
  exact mem_Icc_sourceInitial_graph_iff.mpr
    ⟨optimum_in_initial_box, (mem_sourceSet.mp optimum_feasible).1⟩

/-- The original objective is nonnegative at every point, independently of feasibility. -/
theorem objective_nonneg (x : Fin 2 → ℝ) : 0 ≤ objective x := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `(1, 0)` attains value zero for the original model, before and after the actual limit. -/
theorem attained_minimizer_preserved :
    (![1, 0] ∈ feasible ∩ Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] ∧
      IsMinOn objective (feasible ∩ Icc ![0, 0] ![2, 2]) ![1, 0]) ∧
    (![1, 0] ∈ feasible ∩ variableBox (endpointLimit sumMatrix initial) ∧
      IsMinOn objective (feasible ∩ variableBox (endpointLimit sumMatrix initial)) ![1, 0]) ∧
    objective ![1, 0] = 0 := by
  have hz : objective ![1, 0] = 0 := by norm_num [objective]
  have hi : ![1, 0] ∈ feasible ∩ Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] ∧
      IsMinOn objective (feasible ∩ Icc ![0, 0] ![2, 2]) ![1, 0] := by
    refine ⟨⟨optimum_feasible, optimum_in_initial_box⟩, ?_⟩
    intro y _
    rw [hz]
    exact objective_nonneg y
  have hp := source_preservation sumMatrix ![2] ![0, 0] ![2, 2]
    nonlinearRestriction {0} objective original_nonempty_run
  exact ⟨hi, (hp.2.2.2 ![1, 0]).mpr hi, hz⟩

/-- `(0, 0)` passes the affine, box and integer restrictions but fails the nonlinear restriction. -/
theorem nonlinear_restriction_effective :
    ![0, 0] ∈ sourceSet sumMatrix ![2] univ {0} ∩
      Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] ∧ ![0, 0] ∉ nonlinearRestriction := by
  refine ⟨⟨?_, ?_⟩, by norm_num [nonlinearRestriction]⟩
  · rw [mem_sourceSet]
    refine ⟨?_, mem_univ _, ?_⟩
    · intro i
      fin_cases i
      norm_num [sumMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]
    · intro j _
      exact ⟨0, by fin_cases j <;> norm_num⟩
  · constructor <;> intro j <;> fin_cases j <;> norm_num

/-- `(1/2, 1)` passes the affine, box and nonlinear restrictions but fails integrality of `x₀`. -/
theorem integrality_effective :
    ![(1 / 2 : ℝ), 1] ∈ sourceSet sumMatrix ![2] nonlinearRestriction ∅ ∩
      Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] ∧ ![(1 / 2 : ℝ), 1] ∉ feasible := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_sourceSet]
    refine ⟨?_, by norm_num [nonlinearRestriction], by simp⟩
    intro i
    fin_cases i
    norm_num [sumMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]
  · constructor <;> intro j <;> fin_cases j <;> norm_num
  · intro hx
    obtain ⟨z, hz⟩ := (mem_sourceSet.mp hx).2.2 0 (by simp)
    have hz0 : (0 : ℝ) < (z : ℝ) := by norm_num at hz; linarith
    have hz1 : (z : ℝ) < 1 := by norm_num at hz; linarith
    have hz0' : (0 : ℤ) < z := by exact_mod_cast hz0
    have hz1' : z < (0 : ℤ) + 1 := by exact_mod_cast hz1
    exact (not_le_of_gt hz0') (Int.lt_add_one_iff.mp hz1')

end

end TauCeti.AffineBoundTightening.SourceExamples
