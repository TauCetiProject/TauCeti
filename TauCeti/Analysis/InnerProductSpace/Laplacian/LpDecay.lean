/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.MeanValueInequality
import TauCeti.MeasureTheory.Function.Lp.BallAverage
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz
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

The same mean-value inequality, with the Cauchy–Schwarz bound
`∫_B f ≤ √(μ B) (∫ f²)^(1/2)` in place of the decay of ball averages, bounds a square-integrable
`C²` function with `Δ f ≥ -K` everywhere from above by its `L²` norm:
`f x ≤ (∫ f²)^(1/2) / √(μ (ball 0 r)) + K r² / (2 (n + 2))` for every `x` and `r > 0`
(`TauCeti.le_sqrt_integral_sq_div_add_of_neg_le_laplacian`). The bound depends on `f` only
through `∫ f²` and `K`, so it is uniform over families with bounded `L²` norms. In particular,
`C²` functions with a common bound `|Δ f| ≤ K` that tend to zero in `L²` tend to zero uniformly
(`TauCeti.tendstoUniformly_zero_of_tendsto_integral_sq_of_abs_laplacian_le`).

## Main results

* `TauCeti.eventually_le_of_memLp_of_neg_le_laplacian`: `Δ f ≥ -K` near infinity gives
  `f ≤ ε` near infinity, for every `ε > 0`.
* `TauCeti.tendsto_cocompact_of_memLp_of_abs_laplacian_le`: `|Δ f| ≤ K` near infinity gives
  `f → 0` at infinity.
* `TauCeti.le_sqrt_integral_sq_div_add_of_neg_le_laplacian`: `Δ f ≥ -K` everywhere bounds `f`
  above by its `L²` norm.
* `TauCeti.tendstoUniformly_zero_of_tendsto_integral_sq_of_abs_laplacian_le`: functions with a
  common bound `|Δ f| ≤ K` that tend to zero in `L²` tend to zero uniformly.

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

/-- **A pointwise upper bound from the `L²` norm.** If `f` is `C²` and square integrable with
`Δ f ≥ -K` everywhere, then for every `r > 0` and every point `x`,
`f x ≤ (∫ f²)^(1/2) / √(μ (ball 0 r)) + K r² / (2 (n + 2))`, where `n` is the dimension. -/
theorem le_sqrt_integral_sq_div_add_of_neg_le_laplacian (hf : ContDiff ℝ 2 f)
    (hf2 : MemLp f 2 μ) (hΔ : ∀ x, -K ≤ Δ f x) {r : ℝ} (hr : 0 < r) (x : E) :
    f x ≤ √(∫ y, f y ^ 2 ∂μ) / √(μ.real (ball 0 r)) +
      K * r ^ 2 / (2 * (Module.finrank ℝ E + 2)) := by
  have hmv := mul_le_setIntegral_ball_add_of_neg_le_laplacian (μ := μ) (x₀ := x) (R := r)
    (K := K) hf.contDiffOn hf.continuous.continuousOn fun y _ ↦ hΔ y
  rw [Measure.addHaar_real_ball_center] at hmv
  set V := μ.real (ball (0 : E) r) with hVdef
  have hV : 0 < V := by
    rw [hVdef, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne
  -- Cauchy–Schwarz on the ball: `(∫_B f)² ≤ μ(B) ∫_B f² ≤ V ∫ f²`.
  have hcs : (∫ y in ball x r, f y ∂μ) ^ 2 ≤ V * ∫ y, f y ^ 2 ∂μ := by
    have hfin : IsFiniteMeasure (μ.restrict (ball x r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have h := sq_integral_mul_le_integral_sq_mul_integral_sq (μ := μ.restrict (ball x r))
      (memLp_const (1 : ℝ)) (hf2.restrict (ball x r))
    simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ, Measure.addHaar_real_ball_center] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hV.le)
    exact setIntegral_le_integral hf2.integrable_sq (Eventually.of_forall fun y ↦ sq_nonneg _)
  have hint : ∫ y in ball x r, f y ∂μ ≤ √V * √(∫ y, f y ^ 2 ∂μ) := by
    rw [← Real.sqrt_mul hV.le]
    exact Real.le_sqrt_of_sq_le hcs
  have hsV : √V * √V = V := Real.mul_self_sqrt hV.le
  have hsV0 : 0 < √V := Real.sqrt_pos.2 hV
  have h1 : f x ≤ (∫ y in ball x r, f y ∂μ) / V +
      K * r ^ 2 / (2 * (Module.finrank ℝ E + 2)) := by
    rw [div_add' _ _ _ hV.ne', le_div_iff₀ hV]
    linarith
  have h2 : (∫ y in ball x r, f y ∂μ) / V ≤ √(∫ y, f y ^ 2 ∂μ) / √V := by
    rw [div_le_div_iff₀ hV hsV0]
    calc (∫ y in ball x r, f y ∂μ) * √V ≤ √V * √(∫ y, f y ^ 2 ∂μ) * √V :=
          mul_le_mul_of_nonneg_right hint hsV0.le
      _ = √(∫ y, f y ^ 2 ∂μ) * (√V * √V) := by ring
      _ = √(∫ y, f y ^ 2 ∂μ) * V := by rw [hsV]
  linarith

/-- **Uniform convergence from `L²` convergence and a bound on the Laplacian.** If the functions
`f i` are eventually `C²`, square integrable and satisfy `|Δ (f i)| ≤ K` everywhere, with one
constant `K`, and `∫ (f i)² → 0`, then `f i → 0` uniformly. -/
theorem tendstoUniformly_zero_of_tendsto_integral_sq_of_abs_laplacian_le {ι : Type*}
    {l : Filter ι} {f : ι → E → ℝ} (hf : ∀ᶠ i in l, ContDiff ℝ 2 (f i))
    (hf2 : ∀ᶠ i in l, MemLp (f i) 2 μ) (hΔ : ∀ᶠ i in l, ∀ x, |Δ (f i) x| ≤ K)
    (hl : Tendsto (fun i ↦ ∫ x, f i x ^ 2 ∂μ) l (𝓝 0)) :
    TendstoUniformly f 0 l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  -- A radius `r` with `K₀ r² ≤ ε / 2`, where `K₀ = max K 0`.
  set K₀ := max K 0
  set r := Real.sqrt (ε / 2 / (K₀ + 1))
  have hK₀ : 0 ≤ K₀ := le_max_right _ _
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hKr : K₀ * r ^ 2 ≤ ε / 2 := by
    rw [Real.sq_sqrt (by positivity), mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hcorr : K₀ * r ^ 2 / (2 * (Module.finrank ℝ E + 2)) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ _), mul_nonneg hK₀ (sq_nonneg r)]
  -- Eventually `(∫ (f i)²)^(1/2) / √V < ε / 2`, where `V` is the volume of the ball.
  have hsmall : ∀ᶠ i in l, √(∫ x, f i x ^ 2 ∂μ) / √(μ.real (ball (0 : E) r)) < ε / 2 := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hl
    rw [Real.sqrt_zero] at h
    exact (h.div_const _).eventually (gt_mem_nhds (by simpa using half_pos hε))
  filter_upwards [hf, hf2, hΔ, hsmall] with i hfi hfi2 hΔi hsi x
  rw [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs, abs_lt]
  have hup := le_sqrt_integral_sq_div_add_of_neg_le_laplacian (μ := μ) (K := K₀) hfi hfi2
    (fun y ↦ (neg_le_neg (le_max_left K 0)).trans (neg_le_of_abs_le (hΔi y))) hr x
  -- The same bound for `-f i`, whose Laplacian is `-Δ (f i)`.
  have hlow := le_sqrt_integral_sq_div_add_of_neg_le_laplacian (μ := μ) (K := K₀) (f := -f i)
    hfi.neg hfi2.neg (fun y ↦ by
      rw [laplacian_neg, Pi.neg_apply, neg_le_neg_iff]
      exact (le_abs_self _).trans ((hΔi y).trans (le_max_left K 0))) hr x
  simp only [Pi.neg_apply, neg_sq] at hlow
  constructor <;> linarith

end TauCeti
