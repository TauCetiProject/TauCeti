/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Continuity of the Jacobian `normDet`

For finite-dimensional real inner product spaces `U` and `V`, the `m`-dimensional Jacobian
`LinearMap.normDet` of a linear map `U →L[ℝ] V`, `m = dim U`, depends continuously on the map.
This follows from `normDet² = det (A† A)` (`ContinuousLinearMap.normDet_sq`). Consequently, near an
injective linear map the Jacobian is controlled up to any factor `τ > 1`, uniformly with the
antilipschitz constant.

## Main declarations

* `ContinuousLinearMap.continuous_normDet`: the Jacobian `normDet` is continuous.
* `ContinuousLinearMap.exists_ball_antilipschitzWith_normDet_le`: around an injective linear map
  there is a ball with a uniform antilipschitz constant on which `normDet` varies by a factor at
  most `τ`.
-/

public section

open Function Metric Set
open scoped NNReal Topology

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `m`-dimensional Jacobian `normDet` of a linear map `U →L[ℝ] V`, `m = dim U`, depends
continuously on the map. -/
theorem ContinuousLinearMap.continuous_normDet :
    Continuous fun A : U →L[ℝ] V => A.normDet := by
  have h (A : U →L[ℝ] V) : A.normDet = √((ContinuousLinearMap.adjoint A ∘L A).det) := by
    rw [← A.normDet_sq, RCLike.ofReal_real_eq_id, id, Real.sqrt_sq A.normDet_nonneg]
  simp_rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id)).sqrt

namespace ContinuousLinearMap

/-- Around an injective linear map `B` there is a ball on which the antilipschitz constant is
uniform and the Jacobian varies by a factor at most `τ`: every `C` within distance `ρ` of `B` is
`K`-antilipschitz, and `C.normDet` and `B.normDet` agree up to the factor `τ`. -/
theorem exists_ball_antilipschitzWith_normDet_le (B : U →L[ℝ] V)
    (hB : Injective B) {τ : ℝ} (hτ : 1 < τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : ℝ≥0, ∀ C : U →L[ℝ] V, dist C B < ρ →
      AntilipschitzWith K C ∧ C.normDet ≤ τ * B.normDet ∧ B.normDet ≤ τ * C.normDet := by
  obtain ⟨K₀, hK₀pos, hK₀⟩ := (B : U →ₗ[ℝ] V).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hB)
  have hJ : 0 < B.normDet := lt_of_le_of_ne B.normDet_nonneg
    (Ne.symm fun h => (LinearMap.normDet_eq_zero_iff_ker_ne_bot.1 h) (LinearMap.ker_eq_bot.2 hB))
  -- Continuity of the Jacobian at `B`.
  have hev : ∀ᶠ C in 𝓝 B, C.normDet ∈ Ioo (B.normDet / τ) (τ * B.normDet) :=
    (continuous_normDet.tendsto B).eventually
      (Ioo_mem_nhds (div_lt_self hJ hτ) (lt_mul_of_one_lt_left hJ hτ))
  obtain ⟨ε, hε, hεJ⟩ := Metric.eventually_nhds_iff.1 hev
  have hK₀' : (0 : ℝ) < K₀ := hK₀pos
  refine ⟨min ε (1 / (2 * K₀)), lt_min hε (by positivity), 2 * K₀, fun C hC => ⟨?_, ?_, ?_⟩⟩
  · -- `‖x‖ ≤ K₀ ‖B x‖ ≤ K₀ (‖C x‖ + ‖x‖ / (2 K₀))`.
    refine antilipschitz_of_bound C fun x => ?_
    have h1 : ‖x‖ ≤ K₀ * ‖B x‖ := by simpa using hK₀.le_mul_dist x 0
    have h2 : ‖B - C‖ ≤ 1 / (2 * K₀) := by
      rw [← dist_eq_norm, dist_comm]
      exact hC.le.trans (min_le_right _ _)
    have h3 : ‖B x‖ ≤ ‖C x‖ + 1 / (2 * K₀) * ‖x‖ := by
      calc ‖B x‖ = ‖C x + (B - C) x‖ := by simp
        _ ≤ ‖C x‖ + ‖(B - C) x‖ := norm_add_le _ _
        _ ≤ ‖C x‖ + 1 / (2 * K₀) * ‖x‖ := by
            gcongr
            exact ((B - C).le_opNorm x).trans (by gcongr)
    have h4 : K₀ * (1 / (2 * K₀) * ‖x‖) = ‖x‖ / 2 := by field_simp
    push_cast
    nlinarith
  · exact (hεJ (hC.trans_le (min_le_left _ _))).2.le
  · have h := (hεJ (hC.trans_le (min_le_left _ _))).1
    rw [div_lt_iff₀ (zero_lt_one.trans hτ)] at h
    linarith

end ContinuousLinearMap
