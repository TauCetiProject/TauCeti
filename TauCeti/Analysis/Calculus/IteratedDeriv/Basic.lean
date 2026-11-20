/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Smoothness from derivative towers

A finite or infinite sequence of functions linked by ordinary derivatives gives a `C^m` or smooth
initial function (`TauCeti.contDiff_of_finite_derivative_tower` and
`TauCeti.contDiff_of_derivative_tower`).
-/

public section

open scoped ContDiff

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A finite tower of functions up to order `m` with successive ordinary derivatives and
continuous top level gives a `C^m` zeroth function. -/
theorem contDiff_of_finite_derivative_tower (F : ℕ → 𝕜 → E) (m : ℕ)
    (hF : ∀ k < m, ∀ x, HasDerivAt (F k) (F (k + 1) x) x) (hcont : Continuous (F m)) :
    ContDiff 𝕜 m (F 0) := by
  have hiter : ∀ k ≤ m, iteratedDeriv k (F 0) = F k := by
    intro k hk
    induction k with
    | zero => exact iteratedDeriv_zero
    | succ k ih =>
      rw [iteratedDeriv_succ, ih (Nat.le_of_succ_le hk)]
      exact funext fun x ↦ (hF k hk x).deriv
  refine contDiff_nat_iff_iteratedDeriv.2 ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · rw [hiter k hk]
    rcases hk.eq_or_lt with rfl | hlt
    · exact hcont
    · exact Differentiable.continuous fun x ↦ (hF k hlt x).differentiableAt
  · rw [hiter k hk.le]
    exact fun x ↦ (hF k hk x).differentiableAt

/-- A tower of functions with the stated successive ordinary derivatives gives a smooth zeroth
function. -/
theorem contDiff_of_derivative_tower (F : ℕ → 𝕜 → E)
    (hF : ∀ k x, HasDerivAt (F k) (F (k + 1) x) x) : ContDiff 𝕜 ∞ (F 0) :=
  contDiff_infty.2 fun m ↦ contDiff_of_finite_derivative_tower F m
    (fun k _ x ↦ hF k x) (Differentiable.continuous fun x ↦ (hF m x).differentiableAt)

end TauCeti
