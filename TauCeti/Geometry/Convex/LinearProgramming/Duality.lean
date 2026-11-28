/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Filter.Extr
public import TauCeti.Geometry.Convex.Cone.Farkas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith

/-!
# Strong duality for standard-form linear programs

For a feasible real primal program whose objective is bounded below,
`Matrix.linearProgramming_duality` gives a primal minimizer and a dual maximizer with equal
objective values. For any feasible pair, the objectives agree exactly when every complementary
slackness product vanishes.

If the primal is feasible, a lower bound on its costs yields a dual-feasible point whose value
is at least that bound. If the dual is feasible, an upper bound on its values yields a
primal-feasible point whose cost is at most that bound. Applying these Farkas certificates at the
infimum of the feasible primal costs gives attainment.

## References

* J. M. Borwein and A. S. Lewis, *Convex Analysis and Nonlinear Optimization*, Corollary 5.3.7.
* S. Boyd and L. Vandenberghe, *Convex Optimization*, §§5.2.4 and 5.5.2.
-/

public section

open scoped Matrix

namespace Matrix

variable {K I J : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype I] [Fintype J]

private theorem exists_dual_of_primal_lower_bound
    (A : Matrix I J K) (b : I → K) (c : J → K) (L : K)
    (hfeas : ∃ x, 0 ≤ x ∧ A *ᵥ x = b)
    (hbound : ∀ x, 0 ≤ x → A *ᵥ x = b → L ≤ c ⬝ᵥ x) :
    ∃ y, Aᵀ *ᵥ y ≤ c ∧ L ≤ b ⬝ᵥ y := by
  classical
  have h := (forall_dotProduct_le_iff_exists_vecMul_add_vecMul_eq
    (-1 : Matrix J J K) 0 A b (-c) (-L) (by simpa [neg_mulVec] using hfeas)).mp
    (by simpa [neg_mulVec] using hbound)
  obtain ⟨s, hs, z, heq, hcost⟩ := h
  refine ⟨-z, ?_, ?_⟩
  · rw [mulVec_neg, mulVec_transpose]
    simp only [vecMul_neg, vecMul_one] at heq
    intro j
    have hj := congrFun heq j
    simp only [Pi.add_apply, Pi.neg_apply] at hj ⊢
    have hsj : 0 ≤ s j := hs j
    linarith
  · simp only [dotProduct_zero, zero_add] at hcost
    rw [dotProduct_neg, dotProduct_comm b z]
    linarith

private theorem exists_primal_of_dual_upper_bound
    (A : Matrix I J K) (b : I → K) (c : J → K) (U : K)
    (hfeas : ∃ y, Aᵀ *ᵥ y ≤ c)
    (hbound : ∀ y, Aᵀ *ᵥ y ≤ c → b ⬝ᵥ y ≤ U) :
    ∃ x, 0 ≤ x ∧ A *ᵥ x = b ∧ c ⬝ᵥ x ≤ U := by
  have h := (forall_dotProduct_le_iff_exists_vecMul_add_vecMul_eq
    Aᵀ c (0 : Matrix Unit I K) 0 b U (by simpa using hfeas)).mp (by simpa using hbound)
  obtain ⟨x, hx, z, heq, hcost⟩ := h
  exact ⟨x, hx, by simpa [vecMul_transpose] using heq,
    by simpa [dotProduct_comm c] using hcost⟩

/-- If the primal is infeasible, the dual is either infeasible or unbounded above. -/
theorem dual_infeasible_or_unbounded_of_primal_infeasible
    (A : Matrix I J K) (b : I → K) (c : J → K) (hp : ¬ ∃ x, 0 ≤ x ∧ A *ᵥ x = b) :
    (¬ ∃ y, Aᵀ *ᵥ y ≤ c) ∨ ∀ B : K, ∃ y, Aᵀ *ᵥ y ≤ c ∧ B < b ⬝ᵥ y := by
  classical
  by_cases hd : ∃ y, Aᵀ *ᵥ y ≤ c
  · right
    intro B
    by_contra! hB
    obtain ⟨x, hx, hAx, _⟩ := A.exists_primal_of_dual_upper_bound b c B hd hB
    exact hp ⟨x, hx, hAx⟩
  · exact Or.inl hd

/-- If the dual is infeasible, the primal is either infeasible or unbounded below. -/
theorem primal_infeasible_or_unbounded_of_dual_infeasible
    (A : Matrix I J K) (b : I → K) (c : J → K) (hd : ¬ ∃ y, Aᵀ *ᵥ y ≤ c) :
    (¬ ∃ x, 0 ≤ x ∧ A *ᵥ x = b) ∨ ∀ B : K, ∃ x, 0 ≤ x ∧ A *ᵥ x = b ∧ c ⬝ᵥ x < B := by
  classical
  by_cases hp : ∃ x, 0 ≤ x ∧ A *ᵥ x = b
  · right
    intro B
    by_contra! hB
    obtain ⟨y, hy, _⟩ := A.exists_dual_of_primal_lower_bound b c B hp hB
    exact hd ⟨y, hy⟩
  · exact Or.inl hp

/-- The primal objective minus the dual objective is the sum of slack products. -/
theorem primal_sub_dual_objective_eq_dotProduct_slack {R : Type*} [NonUnitalCommRing R]
    (A : Matrix I J R) {b : I → R} (c x : J → R) (y : I → R) (hAx : A *ᵥ x = b) :
    c ⬝ᵥ x - b ⬝ᵥ y = x ⬝ᵥ (c - Aᵀ *ᵥ y) := by
  rw [dotProduct_sub, dotProduct_transpose_mulVec, hAx, dotProduct_comm x c, dotProduct_comm y b]

/-- Weak duality for a primal-feasible and a dual-feasible point. -/
theorem dual_objective_le_primal_objective {R : Type*} [NonUnitalCommSemiring R] [Preorder R]
    [IsOrderedAddMonoid R] [PosMulMono R] (A : Matrix I J R) {b y : I → R} {c x : J → R}
    (hx : 0 ≤ x) (hAx : A *ᵥ x = b) (hy : Aᵀ *ᵥ y ≤ c) : b ⬝ᵥ y ≤ c ⬝ᵥ x := by
  calc
    b ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by rw [dotProduct_transpose_mulVec, hAx, dotProduct_comm]
    _ ≤ x ⬝ᵥ c := Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hy j) (hx j)
    _ = c ⬝ᵥ x := dotProduct_comm _ _

/-- At a feasible pair, the duality gap vanishes exactly when every slack product vanishes. -/
theorem primal_objective_eq_dual_objective_iff {R : Type*} [NonUnitalCommRing R] [PartialOrder R]
    [IsOrderedAddMonoid R] [PosMulMono R] (A : Matrix I J R) {b y : I → R} {c x : J → R}
    (hx : 0 ≤ x) (hAx : A *ᵥ x = b) (hy : Aᵀ *ᵥ y ≤ c) :
    c ⬝ᵥ x = b ⬝ᵥ y ↔ ∀ j, x j * (c - Aᵀ *ᵥ y) j = 0 := by
  rw [← sub_eq_zero, primal_sub_dual_objective_eq_dotProduct_slack A c x y hAx, dotProduct,
    Finset.sum_eq_zero_iff_of_nonneg]
  · simp
  · exact fun j _ ↦ mul_nonneg (hx j) (sub_nonneg.mpr (hy j))

/-- A feasible real standard-form linear program bounded below has primal and dual optimizers
with equal values. Equality for any feasible pair is characterized by complementary slackness. -/
theorem linearProgramming_duality
    (A : Matrix I J ℝ) (b : I → ℝ) (c : J → ℝ)
    (hfeas : ∃ x : J → ℝ, 0 ≤ x ∧ A *ᵥ x = b)
    (hbdd : ∃ L : ℝ, ∀ x : J → ℝ, 0 ≤ x → A *ᵥ x = b → L ≤ c ⬝ᵥ x) :
    (∃ x : J → ℝ, ∃ y : I → ℝ, 0 ≤ x ∧ A *ᵥ x = b ∧ Aᵀ *ᵥ y ≤ c ∧ c ⬝ᵥ x = b ⬝ᵥ y ∧
      IsMinOn (fun x' ↦ c ⬝ᵥ x') {x' | 0 ≤ x' ∧ A *ᵥ x' = b} x ∧
      IsMaxOn (fun y' ↦ b ⬝ᵥ y') {y' | Aᵀ *ᵥ y' ≤ c} y) ∧
      ∀ x : J → ℝ, ∀ y : I → ℝ, 0 ≤ x → A *ᵥ x = b → Aᵀ *ᵥ y ≤ c →
        (c ⬝ᵥ x = b ⬝ᵥ y ↔ ∀ j, x j * (c - Aᵀ *ᵥ y) j = 0) := by
  refine ⟨?_, fun _ _ ↦ A.primal_objective_eq_dual_objective_iff⟩
  let values := (fun x ↦ c ⬝ᵥ x) '' {x : J → ℝ | 0 ≤ x ∧ A *ᵥ x = b}
  obtain ⟨x₀, hx₀, hAx₀⟩ := hfeas
  obtain ⟨L, hL⟩ := hbdd
  have hne : values.Nonempty := ⟨_, x₀, ⟨hx₀, hAx₀⟩, rfl⟩
  have hlower : BddBelow values := by
    refine ⟨L, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hL x hx.1 hx.2
  obtain ⟨y, hy, hval⟩ := A.exists_dual_of_primal_lower_bound b c (sInf values)
    ⟨x₀, hx₀, hAx₀⟩ (fun x hx hAx ↦ csInf_le hlower ⟨x, ⟨hx, hAx⟩, rfl⟩)
  have hupper (z : I → ℝ) (hz : Aᵀ *ᵥ z ≤ c) : b ⬝ᵥ z ≤ sInf values := by
    apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    exact A.dual_objective_le_primal_objective hx.1 hx.2 hz
  obtain ⟨x, hx, hAx, hcost⟩ := A.exists_primal_of_dual_upper_bound b c (sInf values)
    ⟨y, hy⟩ hupper
  have heq := le_antisymm (hcost.trans hval) (A.dual_objective_le_primal_objective hx hAx hy)
  refine ⟨x, y, hx, hAx, hy, heq, isMinOn_iff.mpr ?_, isMaxOn_iff.mpr ?_⟩
  · exact fun x' hx' ↦ heq.le.trans (A.dual_objective_le_primal_objective hx'.1 hx'.2 hy)
  · exact fun y' hy' ↦ (hupper y' hy').trans hval

end Matrix
