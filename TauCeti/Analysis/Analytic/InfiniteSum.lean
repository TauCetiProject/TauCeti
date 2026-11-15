/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# Normally convergent sums of power series

A family of functions with power series on a common ball can be summed term by term if the
family of coefficient norms, weighted by the radius to the degree, is summable. The resulting
function has the sum of the power series as its power series on the same ball, and is therefore
analytic at the centre. The summation index is arbitrary; in particular this applies to sums
of monomials indexed by multi-indices, with no finite-dimensionality assumption on the domain.

The main result is `TauCeti.hasFPowerSeriesOnBall_tsum`.

Adapted from Michail Karatarakis, `AnalyticTsum.lean` in
`mkaratarakis/mathlib4`, commit `1d51891b5be7ceeca95b4583cad39e0681c5e453`,
`Mathlib/NumberTheory/Transcendental/Baker/`. The argument interchanges the summation over the
family with the summation over homogeneous degrees, using Mathlib's `HasSum.prod_fiberwise`.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- A normally convergent family of power series on a common ball can be summed degree by
degree: the sum has the power series obtained by summing the continuous multilinear maps.
The norm bound is imposed at the radius itself, not just at each point of the open ball. -/
theorem hasFPowerSeriesOnBall_tsum {ι : Type*} {g : ι → E → F}
    {p : ι → FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0} (hr : 0 < r)
    (hg : ∀ i, HasFPowerSeriesOnBall (g i) (p i) x r)
    (hsum : Summable fun ki : ℕ × ι ↦ ‖p ki.2 ki.1‖ * (r : ℝ) ^ ki.1) :
    HasFPowerSeriesOnBall (fun z ↦ ∑' i, g i z) (fun k ↦ ∑' i, p i k) x r := by
  have hrR : (0 : ℝ) < r := hr
  -- First sum the coefficients at each fixed degree, in operator norm.
  have hfibnorm (k : ℕ) : Summable fun i ↦ ‖p i k‖ := by
    have h : Summable fun i ↦ ‖p i k‖ * (r : ℝ) ^ k :=
      hsum.comp_injective (i := fun i ↦ (k, i)) (by intro a b h; simpa using h)
    exact (summable_mul_right_iff (pow_ne_zero k hrR.ne')).mp h
  let q : FormalMultilinearSeries 𝕜 E F := fun k ↦ ∑' i, p i k
  have hqnorm (k : ℕ) : ‖q k‖ ≤ ∑' i, ‖p i k‖ :=
    norm_tsum_le_tsum_norm (hfibnorm k)
  have houter : Summable fun k ↦ ∑' i, ‖p i k‖ * (r : ℝ) ^ k :=
    ((summable_prod_of_nonneg (fun _ ↦ by positivity)).mp hsum).2
  have hradius : (r : ℝ≥0∞) ≤ q.radius := by
    apply q.le_radius_of_summable
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_) houter
    calc
      ‖q k‖ * (r : ℝ) ^ k ≤ (∑' i, ‖p i k‖) * (r : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (hqnorm k) (by positivity)
      _ = ∑' i, ‖p i k‖ * (r : ℝ) ^ k := tsum_mul_right.symm
  refine ⟨hradius, ENNReal.coe_pos.mpr hr, fun {y} hy ↦ ?_⟩
  have hynorm : ‖y‖ < (r : ℝ) := by
    have h : ‖y‖₊ < r := by
      simpa only [mem_eball_zero_iff, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] using hy
    exact_mod_cast h
  -- Absolute convergence permits either order of summation of the evaluated terms.
  have hdbl : Summable fun ki : ℕ × ι ↦ p ki.2 ki.1 (fun _ ↦ y) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun ki ↦ ?_) hsum
    calc
      ‖p ki.2 ki.1 (fun _ ↦ y)‖ ≤ ‖p ki.2 ki.1‖ * ∏ _ : Fin ki.1, ‖y‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖p ki.2 ki.1‖ * ‖y‖ ^ ki.1 := by simp
      _ ≤ ‖p ki.2 ki.1‖ * (r : ℝ) ^ ki.1 := by gcongr
  have hcoeff (k : ℕ) :
      HasSum (fun i ↦ p i k (fun _ ↦ y)) (q k (fun _ ↦ y)) :=
    hasSum_apply (hfibnorm k).of_norm.hasSum _
  have hgoal := hdbl.hasSum.prod_fiberwise hcoeff
  have hswap : HasSum (fun ik : ι × ℕ ↦ p ik.1 ik.2 (fun _ ↦ y))
      (∑' ki : ℕ × ι, p ki.2 ki.1 (fun _ ↦ y)) := by
    simpa [Function.comp_def] using (Equiv.prodComm ι ℕ).hasSum_iff.mpr hdbl.hasSum
  have hvals := hswap.prod_fiberwise fun i ↦ (hg i).hasSum hy
  simpa only [hvals.tsum_eq] using hgoal

end TauCeti
