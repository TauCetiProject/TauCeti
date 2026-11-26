/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.NormalCone

/-!
# Checks: normal cones and constrained minima on the line

Checks of the normal cone and the subdifferential sum rule on `V = ℝ`, where a continuous linear
functional `f` is multiplication by `f 1`.

* For `E(u) = u²` and `C = [1, 2]`, the minimizer is `1` (`isMinOn_sq_Icc`); the normal cone at `1`
  is the set of `f` with `f 1 ≤ 0` (`mem_normalCone_Icc_one_iff`), so `-2 ∈ N_C(1)`
  (`neg_two_smul_mem_normalCone`), and `0 = 2 + (-2) ∈ ∂E(1) + N_C(1)`
  (`zero_mem_subdifferential_sq_add_normalCone`), as the sum rule predicts at the constrained
  minimizer.
* For `E(u) = |u|` and `C = ℝ`, `0 ∈ ∂E(0)` (`zero_mem_subdifferential_abs`): the unconstrained
  nonsmooth condition at the minimizer `0`.
-/

public section

open Set Pointwise

namespace TauCeti.Examples.NormalCone

/-- A functional on `ℝ` is multiplication by its value at `1`. -/
private theorem apply_eq_mul (f : StrongDual ℝ ℝ) (v : ℝ) : f v = v * f 1 := by
  simpa using f.map_smul v 1

/-- `u ↦ u²` is minimized on `[1, 2]` at `1`. -/
theorem isMinOn_sq_Icc : IsMinOn (fun u : ℝ ↦ u ^ 2) (Icc 1 2) 1 :=
  isMinOn_iff.2 fun v hv ↦ by nlinarith [hv.1]

/-- The normal cone of `[1, 2]` at `1` is the set of functionals with `f 1 ≤ 0`. -/
theorem mem_normalCone_Icc_one_iff {f : StrongDual ℝ ℝ} :
    f ∈ normalCone (Icc (1 : ℝ) 2) 1 ↔ f 1 ≤ 0 := by
  rw [mem_normalCone_iff]
  refine ⟨fun h ↦ ?_, fun h v hv ↦ ?_⟩
  · have h2 := h 2 ⟨by norm_num, le_rfl⟩
    norm_num at h2
    exact h2
  rw [apply_eq_mul f]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hv.1]) h

/-- `-2 ∈ N_{[1, 2]}(1)`. -/
theorem neg_two_smul_mem_normalCone :
    (-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ ∈ normalCone (Icc (1 : ℝ) 2) 1 := by
  rw [mem_normalCone_Icc_one_iff]
  norm_num

/-- The derivative `2` of `u²` at `1` is a subgradient there. -/
theorem two_smul_mem_subdifferential_sq :
    (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ ∈
      subdifferential (topDualPairing ℝ ℝ).flip (fun u : ℝ ↦ ((u ^ 2 : ℝ) : EReal)) 1 := by
  rw [mem_subdifferential_coe_iff]
  intro v
  simp only [LinearMap.flip_apply, topDualPairing_apply, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul]
  nlinarith [sq_nonneg (v - 1)]

/-- `0 = 2 + (-2) ∈ ∂E(1) + N_{[1, 2]}(1)` for `E(u) = u²`, the first-order condition at the
constrained minimizer `1`. -/
theorem zero_mem_subdifferential_sq_add_normalCone :
    (0 : StrongDual ℝ ℝ) ∈
      subdifferential (topDualPairing ℝ ℝ).flip (fun u : ℝ ↦ ((u ^ 2 : ℝ) : EReal)) 1 +
        normalCone (Icc (1 : ℝ) 2) 1 :=
  ⟨_, two_smul_mem_subdifferential_sq, _, neg_two_smul_mem_normalCone, by
    simp [← add_smul]⟩

/-- `0 ∈ ∂|·|(0)`. -/
theorem zero_mem_subdifferential_abs :
    (0 : StrongDual ℝ ℝ) ∈
      subdifferential (topDualPairing ℝ ℝ).flip (fun u : ℝ ↦ ((|u| : ℝ) : EReal)) 0 := by
  rw [mem_subdifferential_coe_iff]
  intro v
  simp

end TauCeti.Examples.NormalCone
