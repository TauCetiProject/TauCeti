/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.LinearProgramming.Duality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Examples of optimality and unboundedness in linear programming

On the unit simplex the cost vector `(1, 2)` gives value one at the vertex `(1, 0)`.
The dual witness `y = 1` certifies optimality by weak duality. On the nonnegative diagonal
the cost vector `(-1, 0)` instead decreases without bound, and the dual is infeasible.
-/

@[expose] public section

open scoped Matrix

namespace TauCeti.Examples.LinearProgramming

/-- The simplex constraint has both coefficients equal to one. -/
def sumRow : Matrix (Fin 1) (Fin 2) ℝ := fun _ _ ↦ 1

/-- The objective charges twice as much for the second variable. -/
def cost : Fin 2 → ℝ := ![1, 2]

/-- The first coordinate vertex of the unit simplex. -/
def vertex : Fin 2 → ℝ := ![1, 0]

/-- The feasible witnesses `(1,0)` and `1` have common value one and satisfy both slackness
equations for the unit simplex with cost `(1,2)`. -/
theorem vertex_certificate :
    0 ≤ vertex ∧ sumRow *ᵥ vertex = 1 ∧
    sumRowᵀ *ᵥ (1 : Fin 1 → ℝ) ≤ cost ∧
    cost ⬝ᵥ vertex = 1 ∧ (1 : Fin 1 → ℝ) ⬝ᵥ 1 = 1 ∧
    ∀ j, vertex j * (cost j - (sumRowᵀ *ᵥ (1 : Fin 1 → ℝ)) j) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [vertex]
  · funext i
    norm_num [sumRow, vertex, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro j
    fin_cases j <;> norm_num [sumRow, cost, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  · norm_num [cost, vertex, dotProduct, Fin.sum_univ_two]
  · norm_num [dotProduct, Fin.sum_univ_one]
  · intro j
    fin_cases j <;> norm_num [sumRow, vertex, cost, Matrix.mulVec, dotProduct, Fin.sum_univ_one]

/-- The exhibited vertex and dual point actually attain the minimum and maximum. -/
theorem vertex_and_one_optimal :
    IsMinOn (fun x ↦ cost ⬝ᵥ x) {x | 0 ≤ x ∧ sumRow *ᵥ x = 1} vertex ∧
    IsMaxOn (fun y ↦ (1 : Fin 1 → ℝ) ⬝ᵥ y) {y | sumRowᵀ *ᵥ y ≤ cost} 1 := by
  obtain ⟨hx, hAx, hy, hv, hw, _⟩ := vertex_certificate
  have heq := hv.trans hw.symm
  refine ⟨isMinOn_iff.mpr ?_, isMaxOn_iff.mpr ?_⟩
  · exact fun x hx' ↦ heq.le.trans (sumRow.dual_objective_le_primal_objective hx'.1 hx'.2 hy)
  · exact fun y hy' ↦ (sumRow.dual_objective_le_primal_objective hx hAx hy').trans heq.le

/-- The equality constraint for the diagonal. -/
def differenceRow : Matrix (Fin 1) (Fin 2) ℝ := fun _ ↦ ![1, -1]

/-- The objective on the diagonal is the negative of its first coordinate. -/
def negativeCost : Fin 2 → ℝ := ![-1, 0]

/-- The ray `(t,t)`, `t ≥ 0`, is primal feasible with objective `-t`. Its dual would require
`0 ≤ y ≤ -1`. -/
theorem diagonal_unbounded_and_dual_infeasible :
    (∀ B : ℝ, ∃ x : Fin 2 → ℝ, 0 ≤ x ∧ differenceRow *ᵥ x = 0 ∧ negativeCost ⬝ᵥ x < B) ∧
    ¬ ∃ y : Fin 1 → ℝ, differenceRowᵀ *ᵥ y ≤ negativeCost := by
  constructor
  · intro B
    let t := max 0 (-B) + 1
    have ht : 0 ≤ t := add_nonneg (le_max_left ..) zero_le_one
    refine ⟨fun _ ↦ t, fun _ ↦ ht, ?_, ?_⟩
    · funext i
      norm_num [differenceRow, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · have hlt : -B < t := lt_of_le_of_lt (le_max_right ..) (lt_add_one _)
      norm_num [negativeCost, dotProduct, Fin.sum_univ_two]
      linarith
  · rintro ⟨y, hy⟩
    have h₀ := hy 0
    have h₁ := hy 1
    norm_num [differenceRow, negativeCost, Matrix.mulVec, dotProduct, Fin.sum_univ_one] at h₀ h₁
    linarith

end TauCeti.Examples.LinearProgramming
