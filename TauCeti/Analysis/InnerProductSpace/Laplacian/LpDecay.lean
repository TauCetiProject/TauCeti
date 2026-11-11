/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.MeanValueInequality
import TauCeti.MeasureTheory.Function.Lp.BallAverage
import TauCeti.Topology.MetricSpace.Bounded

/-!
# Decay at infinity of `Lᵖ` functions with bounded Laplacian

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `f : E → ℝ` lie in `Lᵖ(μ)` for some `1 ≤ p < ∞`. Membership in `Lᵖ` alone does not make `f`
small at infinity: `f` may have tall, thin spikes. A one-sided bound on the Laplacian excludes
upward spikes. If `f` is `C²` near infinity and `Δ f ≥ -K` there, then `f` is eventually at
most any `ε > 0` (`TauCeti.eventually_le_of_memLp_of_neg_le_laplacian`). Consequently, a
two-sided bound `|Δ f| ≤ K` near infinity forces `f → 0` at infinity
(`TauCeti.tendsto_cocompact_of_memLp_of_abs_laplacian_le`).

The proof combines two estimates on a ball `B = ball x R` of a fixed small radius. The
mean-value inequality for `Δ f ≥ -K`
(`TauCeti.mul_le_setIntegral_ball_add_of_neg_le_laplacian`) bounds `f x` by the average of `f`
over `B` plus `K R² / (2 (n + 2))`. The average of an `Lᵖ` function over balls of radius `R`
tends to zero at infinity (`TauCeti.tendsto_ballAverage_cocompact`). Choosing `R` with
`K R² ≤ ε` gives `f x ≤ ε` for all far points `x`.

This is how a solution of a semilinear elliptic equation, known to be square integrable from a
variational construction, is shown to satisfy a boundary condition at infinity: the equation
bounds the Laplacian once the solution is bounded, and this file turns that bound into decay.

## Main results

* `TauCeti.eventually_le_of_memLp_of_neg_le_laplacian`: `Δ f ≥ -K` near infinity gives
  `f ≤ ε` near infinity, for every `ε > 0`.
* `TauCeti.tendsto_cocompact_of_memLp_of_abs_laplacian_le`: `|Δ f| ≤ K` near infinity gives
  `f → 0` at infinity.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.1 (the mean-value inequality).
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Filter Topology
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → ℝ}
  {p : ℝ≥0∞} {K : ℝ}

/-- **Upper bound at infinity from a lower bound on the Laplacian.** If `f` lies in `Lᵖ`,
`1 ≤ p < ∞`, and is `C²` with `Δ f ≥ -K` outside a compact set, then for every `ε > 0` the
function `f` is at most `ε` outside some compact set. -/
theorem eventually_le_of_memLp_of_neg_le_laplacian
    (hf : ∀ᶠ x in cocompact E, ContDiffAt ℝ 2 f x) (hfp : MemLp f p μ) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hΔ : ∀ᶠ x in cocompact E, -K ≤ Δ f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in cocompact E, f x ≤ ε := by
  -- A radius `R` with `K₀ R² ≤ ε`, where `K₀ = max K 0`.
  set K₀ := max K 0
  set R := Real.sqrt (ε / (K₀ + 1))
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hKR : K₀ * R ^ 2 ≤ ε := by
    rw [Real.sq_sqrt (by positivity), mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  -- Far away, the hypotheses hold on the whole closed ball of radius `R`, and the average of `f`
  -- over the open ball is less than `ε / 2`.
  have hballs : ∀ᶠ x in cocompact E, ∀ y ∈ closedBall x R, ContDiffAt ℝ 2 f y ∧ -K ≤ Δ f y :=
    (cobounded_eq_cocompact (α := E) ▸ tendsto_closedBall_cobounded_smallSets R).eventually
      (eventually_smallSets_forall.2 (hf.and hΔ))
  have havg := (tendsto_order.1 (tendsto_ballAverage_cocompact hfp hp hp' R)).2 (ε / 2)
    (half_pos hε)
  filter_upwards [hballs, havg] with x hx havgx
  have hmv := mul_le_setIntegral_ball_add_of_neg_le_laplacian (μ := μ) (K := K₀)
    (fun y hy => (hx y (ball_subset_closedBall hy)).1.contDiffWithinAt)
    (fun y hy => (hx y hy).1.continuousAt.continuousWithinAt)
    (fun y hy => (neg_le_neg (le_max_left K 0)).trans (hx y (ball_subset_closedBall hy)).2)
  have hpos : 0 < μ.real (ball x R) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ x hR).ne' measure_ball_lt_top.ne
  -- Dividing by the measure of the ball: `f x ≤ ⨍ f + K₀ R² / (2 (n + 2))`.
  have hle : f x ≤ ballAverage μ R f x + K₀ * R ^ 2 / (2 * (Module.finrank ℝ E + 2)) := by
    rw [ballAverage_apply, setAverage_eq, smul_eq_mul, ← div_eq_inv_mul,
      div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
    linarith
  have hcorr : K₀ * R ^ 2 / (2 * (Module.finrank ℝ E + 2)) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ _), mul_nonneg hK₀ (sq_nonneg R)]
  linarith

/-- **Decay at infinity from a bound on the Laplacian.** If `f` lies in `Lᵖ`, `1 ≤ p < ∞`, and is
`C²` with `|Δ f| ≤ K` outside a compact set, then `f → 0` at infinity. -/
theorem tendsto_cocompact_of_memLp_of_abs_laplacian_le
    (hf : ∀ᶠ x in cocompact E, ContDiffAt ℝ 2 f x) (hfp : MemLp f p μ) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hΔ : ∀ᶠ x in cocompact E, |Δ f x| ≤ K) :
    Tendsto f (cocompact E) (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- Apply the upper bound to `-f`, whose Laplacian is `-Δ f`.
    have h := eventually_le_of_memLp_of_neg_le_laplacian (f := -f) (K := K)
      (hf.mono fun x hx => hx.neg)
      hfp.neg hp hp' (hΔ.mono fun x hx => by
        rw [laplacian_neg, Pi.neg_apply, neg_le_neg_iff]
        exact (le_abs_self _).trans hx) (half_pos (neg_pos.2 ha))
    filter_upwards [h] with x hx
    simp only [Pi.neg_apply] at hx
    linarith
  · filter_upwards [eventually_le_of_memLp_of_neg_le_laplacian (μ := μ) hf hfp hp hp'
      (hΔ.mono fun x hx => neg_le_of_abs_le hx) (half_pos ha)] with x hx
    linarith

end TauCeti
