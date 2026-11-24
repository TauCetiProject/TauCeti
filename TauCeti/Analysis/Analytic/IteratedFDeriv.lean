/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Canonical Taylor series of analytic functions via `iteratedFDeriv`

If `f : E → F` into a complete normed space admits a formal multilinear series `p` on `eball x r`
(within a set `s` of unique differentiability containing `x`), Mathlib's
`HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace` expresses its `n`-th
iterated Fréchet derivative at `x` as the symmetrization
`v ↦ ∑ σ : Perm (Fin n), p n (v ∘ σ)`.

Over `ℝ` or `ℂ` (`[RCLike 𝕜]`), where `‖(n ! : 𝕜)‖ = n !`, the triangle inequality and invariance
of `∏ i, ‖v i‖` under permutations imply `‖(n ! : 𝕜)⁻¹ • iteratedFDerivWithin 𝕜 n f s x‖ ≤ ‖p n‖`
for every `n`, so Mathlib's `FormalMultilinearSeries.radius_le_of_le` shows that the canonical
symmetric Taylor series `n ↦ (n ! : 𝕜)⁻¹ • iteratedFDerivWithin 𝕜 n f s x` has convergence radius
at least `p.radius` (and hence at least `r`) and agrees with `p` on every diagonal `(y, …, y)`.
This fails over non-Archimedean fields, where `‖(n ! : 𝕜)⁻¹‖` grows exponentially in `n`.

## Main declarations

* `HasFPowerSeriesWithinOnBall.inv_factorial_smul_iteratedFDerivWithin`: passing from any formal
  multilinear series on `eball x r` within `s` to the canonical symmetric Taylor series
  `n ↦ (n ! : 𝕜)⁻¹ • iteratedFDerivWithin 𝕜 n f s x` without shrinking the radius.
* `HasFPowerSeriesOnBall.inv_factorial_smul_iteratedFDeriv`: the unconditional ball version for
  `n ↦ (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x`.
-/

public section

open scoped ENNReal Nat

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞}

/-- Over `ℝ` or `ℂ` and into a complete space, any formal multilinear series `p` representing `f`
on `eball x r` within a set `s` of unique differentiability containing `x` can be replaced, with
no loss of radius, by the canonical symmetric Taylor series
`n ↦ (n ! : 𝕜)⁻¹ • iteratedFDerivWithin 𝕜 n f s x`. -/
theorem HasFPowerSeriesWithinOnBall.inv_factorial_smul_iteratedFDerivWithin
    (hp : HasFPowerSeriesWithinOnBall f p s x r) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasFPowerSeriesWithinOnBall f
      (fun n ↦ (n ! : 𝕜)⁻¹ • iteratedFDerivWithin 𝕜 n f s x) s x r where
  r_le := by
    refine hp.r_le.trans (FormalMultilinearSeries.radius_le_of_le fun n ↦ ?_)
    refine ContinuousMultilinearMap.opNorm_le_bound (ContinuousMultilinearMap.opNorm_nonneg _)
      fun v ↦ ?_
    rw [smul_apply, hp.iteratedFDerivWithin_eq_sum_of_completeSpace hs hx]
    simp only [norm_smul, norm_inv, RCLike.norm_natCast]
    calc (n ! : ℝ)⁻¹ * ‖∑ σ : Equiv.Perm (Fin n), p n (fun i ↦ v (σ i))‖
      _ ≤ (n ! : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i ↦ v (σ i))‖ := by
          gcongr
          exact norm_sum_le _ _
      _ ≤ (n ! : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v (σ i)‖ := by
          gcongr
          exact (p n).le_opNorm _
      _ = (n ! : ℝ)⁻¹ * ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ := by
          congr 1
          refine Finset.sum_congr rfl fun σ _ ↦ ?_
          rw [Fintype.prod_equiv σ _ (fun i ↦ ‖v i‖) (fun _ ↦ rfl)]
      _ = ‖p n‖ * ∏ i, ‖v i‖ := by
          simp [Fintype.card_perm, ← mul_assoc, Nat.factorial_ne_zero]
  r_pos := hp.r_pos
  hasSum {y} hys hy := by
    convert hp.hasSum hys hy using 1
    ext n
    rw [smul_apply, hp.iteratedFDerivWithin_eq_sum_of_completeSpace hs hx]
    simp [Fintype.card_perm, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, Nat.factorial_ne_zero]

/-- Over `ℝ` or `ℂ` and into a complete space, any formal multilinear series `p` representing `f`
on `eball x r` can be replaced, with no loss of radius, by the canonical symmetric Taylor series
`n ↦ (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x`. -/
theorem HasFPowerSeriesOnBall.inv_factorial_smul_iteratedFDeriv
    (hp : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x) x r :=
  hasFPowerSeriesWithinOnBall_univ.1 <| by
    simpa only [← iteratedFDerivWithin_univ] using
      hp.hasFPowerSeriesWithinOnBall.inv_factorial_smul_iteratedFDerivWithin
        uniqueDiffOn_univ (Set.mem_univ x)
