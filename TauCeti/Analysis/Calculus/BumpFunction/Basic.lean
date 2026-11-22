/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Bump functions with support in a ball

On a real normed space with smooth bump functions, every open ball contains the topological
support of a smooth bump function centred at its centre. Multiplying the identity by such a bump
gives a smooth map into the ball that is the identity near its centre; composing with it turns a
map defined only on a ball into a globally defined map with the same germ at the centre.
Conversely, the rescaled bump `φ (R⁻¹ ·)` of a bump `φ` centred at `0` vanishes off the ball of
radius `R φ.rOut`.

## Main results

* `TauCeti.exists_contDiffBump_tsupport_subset_ball`: a bump centred at `c` whose topological
  support lies in the ball of radius `r` around `c`.
* `TauCeti.exists_contDiff_eventuallyEq_id_forall_mem_ball`: a smooth map into the ball of radius
  `r` about `0` which is the identity near `0`.
* `ContDiff.exists_contDiff_bdd_deriv_eventuallyEq`: a `C¹` function on `ℝ` agrees near `[-M, M]`
  with a `C¹` function of bounded derivative.
* `ContDiffBump.apply_inv_smul_eq_zero_of_le_norm`, `ContDiffBump.ofReal_apply_inv_smul_eq_zero`:
  the rescaled bump `φ (R⁻¹ ·)`, `R > 0`, vanishes off the ball of radius `R φ.rOut`.
-/

public section

open Metric Filter
open scoped ContDiff NNReal Topology

namespace TauCeti

/-- A smooth bump function centred at `c` whose topological support lies in the ball of radius
`r > 0` around `c`. -/
theorem exists_contDiffBump_tsupport_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] (c : E) {r : ℝ} (hr : 0 < r) :
    ∃ b : ContDiffBump c, tsupport b ⊆ ball c r :=
  -- the bump of radii `r / 4` and `r / 2`
  ⟨⟨r / 4, r / 2, by positivity, by linarith⟩, by
    rw [ContDiffBump.tsupport_eq]
    exact closedBall_subset_ball (half_lt_self hr)⟩

/-- A smooth self-map of a real normed space with smooth bump functions which is the identity near
`0` and takes values in the ball of radius `r > 0` about `0`. It is `x ↦ b(x) • x` for a bump `b`
equal to `1` near `0` and supported in that ball. -/
theorem exists_contDiff_eventuallyEq_id_forall_mem_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [HasContDiffBump E] {r : ℝ} (hr : 0 < r) :
    ∃ ρ : E → E, ContDiff ℝ ∞ ρ ∧ ρ =ᶠ[𝓝 0] id ∧ ∀ x, ρ x ∈ ball (0 : E) r := by
  let b : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨fun x ↦ b x • x, b.contDiff.smul contDiff_id, ?_, fun x ↦ ?_⟩
  · filter_upwards [b.eventuallyEq_one] with x hx
    simp [hx]
  · dsimp only
    rcases lt_or_ge ‖x‖ r with hx | hx
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg b.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg x) b.le_one).trans_lt hx
    · rw [b.zero_of_le_dist (by simpa using hx), zero_smul]
      exact mem_ball_self hr

/-- A `C¹` function `Φ : ℝ → G` agrees near every point of `[-M, M]` with a `C¹` function whose
derivative is bounded, namely its product with a bump function equal to one on a neighbourhood of
`[-M, M]`. The product agrees with `Φ` at `0`. -/
theorem _root_.ContDiff.exists_contDiff_bdd_deriv_eventuallyEq {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {Φ : ℝ → G} (hΦ : ContDiff ℝ 1 Φ) (M : ℝ) :
    ∃ F : ℝ → G, ∃ K : ℝ≥0, ContDiff ℝ 1 F ∧ (∀ t, ‖deriv F t‖₊ ≤ K) ∧
      (∀ t, |t| ≤ M → F =ᶠ[𝓝 t] Φ) ∧ F 0 = Φ 0 := by
  set R := |M| + 1
  let ψ : ContDiffBump (0 : ℝ) := ⟨R, R + 1, by positivity, by linarith⟩
  have hF : ContDiff ℝ 1 fun t => ψ t • Φ t := ψ.contDiff.smul hΦ
  obtain ⟨K, hK⟩ := (hF.continuous_deriv le_rfl).bounded_above_of_compact_support
    (ψ.hasCompactSupport.smul_right (f' := Φ)).deriv
  refine ⟨fun t => ψ t • Φ t, K.toNNReal, hF, fun t => ?_, fun t ht => ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact (hK t).trans (Real.le_coe_toNNReal K)
  · have ht' : t ∈ ball (0 : ℝ) R := by
      rw [mem_ball, Real.dist_eq, sub_zero]
      linarith [le_abs_self M]
    filter_upwards [isOpen_ball.mem_nhds ht'] with s hs
    rw [ψ.one_of_mem_closedBall (ball_subset_closedBall hs), one_smul]
  · simp only [ψ.one_of_mem_closedBall (mem_closedBall_self ψ.rIn_pos.le), one_smul]

end TauCeti

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  (φ : ContDiffBump (0 : E))

/-- The rescaled bump function `φ (R⁻¹ ·)`, `R > 0`, vanishes outside the open ball of radius
`R φ.rOut`. -/
theorem apply_inv_smul_eq_zero_of_le_norm {R : ℝ} (hR : 0 < R) {ξ : E}
    (hξ : R * φ.rOut ≤ ‖ξ‖) : φ (R⁻¹ • ξ) = 0 :=
  φ.zero_of_le_dist (by
    rwa [dist_zero_right, TauCeti.norm_inv_smul_of_nonneg hR.le, le_div_iff₀ hR, mul_comm])

/-- The complex rescaled bump function `φ (R⁻¹ ·)`, `R > 0`, vanishes outside the closed ball of
radius `R φ.rOut`. -/
theorem ofReal_apply_inv_smul_eq_zero {R : ℝ} (hR : 0 < R) :
    ∀ ξ ∈ (Metric.closedBall (0 : E) (R * φ.rOut))ᶜ, (φ (R⁻¹ • ξ) : ℂ) = 0 := fun ξ hξ ↦ by
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hξ
  rw [φ.apply_inv_smul_eq_zero_of_le_norm hR hξ.le, Complex.ofReal_zero]

end ContDiffBump
