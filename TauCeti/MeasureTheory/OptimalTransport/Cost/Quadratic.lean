/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Cyclical monotonicity for quadratic transport cost

For a real inner product space, the quadratic cost decomposes as
`‖x-y‖²/2 = ‖x‖²/2 - ⟪x,y⟫ + ‖y‖²/2`. The two squared-norm terms cancel under every
permutation of targets. Thus transport-cost cyclical monotonicity is exactly the usual
cyclical monotonicity inequality for the inner-product pairing. This bridge lets convex
subgradient arguments apply to supports and contact sets of quadratic optimal plans.

The decomposition is the standard starting point of Brenier's theorem; see C. Villani,
*Topics in Optimal Transportation*, §2.1.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Quadratic-cost cyclical monotonicity is cyclical monotonicity for the negative
inner-product pairing. -/
theorem isCyclicallyMonotone_quadratic_iff (S : Set (E × E)) :
    IsCyclicallyMonotone (fun (p : E × E) ↦ ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      IsCyclicallyMonotone (fun (p : E × E) ↦ -⟪p.1, p.2⟫_ℝ) S := by
  have hcost : (fun (p : E × E) ↦ ‖p.1 - p.2‖ ^ 2 / 2) =
      (fun (p : E × E) ↦ -⟪p.1, p.2⟫_ℝ + ‖p.1‖ ^ 2 / 2 + ‖p.2‖ ^ 2 / 2) := by
    funext p
    rw [norm_sub_sq_real]
    ring
  rw [hcost]
  exact isCyclicallyMonotone_add_split_iff (fun p : E × E ↦ -⟪p.1, p.2⟫_ℝ)
    (fun x ↦ ‖x‖ ^ 2 / 2) (fun y ↦ ‖y‖ ^ 2 / 2) S

/-- The finite-family form of quadratic-cost cyclical monotonicity: matching each
source to its original target maximizes the sum of inner products over permutations. -/
theorem isCyclicallyMonotone_quadratic_iff_inner (S : Set (E × E)) :
    IsCyclicallyMonotone (fun (p : E × E) ↦ ‖p.1 - p.2‖ ^ 2 / 2) S ↔
      ∀ (n : ℕ) (x y : Fin n → E), (∀ i, (x i, y i) ∈ S) →
        ∀ σ : Equiv.Perm (Fin n),
          (∑ i, ⟪x i, y (σ i)⟫_ℝ) ≤ ∑ i, ⟪x i, y i⟫_ℝ := by
  rw [isCyclicallyMonotone_quadratic_iff, isCyclicallyMonotone_iff]
  simp only [Finset.sum_neg_distrib, neg_le_neg_iff]

/-- Two points in a cyclically monotone set for quadratic cost form a monotone pair:
their source and target differences have nonnegative inner product. -/
theorem inner_sub_nonneg_of_isCyclicallyMonotone_quadratic {S : Set (E × E)}
    (hS : IsCyclicallyMonotone (fun p : E × E ↦ ‖p.1 - p.2‖ ^ 2 / 2) S)
    {x₁ x₂ y₁ y₂ : E} (h₁ : (x₁, y₁) ∈ S) (h₂ : (x₂, y₂) ∈ S) :
    0 ≤ ⟪x₁ - x₂, y₁ - y₂⟫_ℝ := by
  have h := ((isCyclicallyMonotone_quadratic_iff S).mp hS).add_le_add_swap h₁ h₂
  simp only [inner_sub_left, inner_sub_right]
  linarith

end TauCeti
