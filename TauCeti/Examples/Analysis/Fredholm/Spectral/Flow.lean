/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.FiniteDimensional
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.ODE.TrajectoryOperator.Tanh
import TauCeti.Analysis.SpecialFunctions.Hyperbolic

/-!
# The spectral flow of `A(s) = tanh s`

The scalar path `A(s) = tanh s`, acting on a finite-dimensional real inner product space `H` as
`tanh s • 1`, has its one eigenvalue cross `0` upwards at `s = 0`. Its spectral flow from any
`a < 0` to any `b ≥ 0` is therefore the dimension of `H`, and `1` on the line itself. Reversing
the path, `s ↦ tanh (-s) = -tanh s`, gives `-1`. These are the values on which the sign convention
of `TauCeti.spectralFlow` is tested: positive crossings count positively.

They follow from the formula `TauCeti.spectralFlow_algebraMap_comp` for scalar paths, since `tanh`
is continuous and `tanh s` has the sign of `s`. The same path is the coefficient of the trajectory
operator `d/ds - tanh s` on `W^{1,2}(ℝ, H) → L²(ℝ, H)`, whose index is `-dim H`
(`TauCeti.WeakDerivStep.index_trajectoryOperator_neg_tanh_smul_id`). So in this example the index
of `d/ds - A` is minus the spectral flow of `A`
(`TauCeti.SpectralFlowTanhExample.index_trajectoryOperator_neg_tanh_smul_id_eq_neg_spectralFlow`).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti.SpectralFlowTanhExample

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The spectral flow of `s ↦ tanh s • 1` from `a < 0` to `b ≥ 0` is the dimension of `H`. -/
theorem spectralFlow_tanh {a b : ℝ} (ha : a < 0) (hb : 0 ≤ b) :
    spectralFlow (fun s ↦ algebraMap ℝ (H →L[ℝ] H) (Real.tanh s)) a b =
      (Module.finrank ℝ H : ℤ) := by
  rw [spectralFlow_algebraMap_comp (ha.le.trans hb) Real.continuous_tanh.continuousOn]
  simp [Real.tanh_nonneg_iff, hb, not_le.2 ha]

/-- The reversed path `s ↦ tanh (-s) • 1` from `a ≤ 0` to `b > 0` has spectral flow minus the
dimension of `H`. -/
theorem spectralFlow_tanh_neg {a b : ℝ} (ha : a ≤ 0) (hb : 0 < b) :
    spectralFlow (fun s ↦ algebraMap ℝ (H →L[ℝ] H) (Real.tanh (-s))) a b =
      -(Module.finrank ℝ H : ℤ) := by
  rw [spectralFlow_algebraMap_comp (f := fun s ↦ Real.tanh (-s)) (ha.trans hb.le)
    (Real.continuous_tanh.comp continuous_neg).continuousOn]
  simp only [Real.tanh_nonneg_iff]
  simp [ha, not_le.2 hb]

/-- For `A(s) = tanh s • 1`, the trajectory operator `d/ds - A` from `W^{1,2}(ℝ, H)` to `L²(ℝ, H)`
has index minus the spectral flow of `A` from any `a < 0` to any `b ≥ 0`: both are computed, as
`-dim H` and `dim H`. -/
theorem index_trajectoryOperator_neg_tanh_smul_id_eq_neg_spectralFlow
    {AL : Lp (H →L[ℝ] H) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ H) {a b : ℝ} (ha : a < 0) (hb : 0 ≤ b) :
    (WeakDerivStep.trajectoryOperator (p := 2) AL).index =
      -spectralFlow (fun s ↦ algebraMap ℝ (H →L[ℝ] H) (Real.tanh s)) a b := by
  rw [WeakDerivStep.index_trajectoryOperator_neg_tanh_smul_id hAL, spectralFlow_tanh ha hb]

/-- On the real line, `A(s) = tanh s` crosses upward once: its spectral flow from `-1` to `1` is
`1`. -/
example : spectralFlow (fun s ↦ algebraMap ℝ (ℝ →L[ℝ] ℝ) (Real.tanh s)) (-1) 1 = 1 := by
  rw [spectralFlow_tanh (by norm_num) zero_le_one, Module.finrank_self, Nat.cast_one]

/-- On the real line, the reversed path `s ↦ tanh (-s)` has spectral flow `-1` from `-1` to `1`. -/
example : spectralFlow (fun s ↦ algebraMap ℝ (ℝ →L[ℝ] ℝ) (Real.tanh (-s))) (-1) 1 = -1 := by
  rw [spectralFlow_tanh_neg (by norm_num) zero_lt_one, Module.finrank_self, Nat.cast_one]

end TauCeti.SpectralFlowTanhExample
