/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The maximum principle for the sub-mean-value property

Let `E` be a nontrivial finite-dimensional real normed space with an additive Haar measure `μ`.
This file proves that a function `u`, continuous on a compact set `K`, with
`u x ≤ ⨍ y in ball x r, u y ∂μ` for arbitrarily small `r > 0` at every interior point `x` of `K`,
attains its maximum over `K` on `frontier K`. No differentiability is assumed, so this applies to
continuous subharmonic functions in their mean-value formulation, and to differences of a
continuous function with the mean-value property and a harmonic function.

## The argument

Among the points where the maximum `M` is attained, take one, `z`, farthest from a fixed maximum
point. If `z` were interior, then on a small ball about `z` contained in `K` the continuous
function `u ≤ M` would have average at least `M`, so by the equality case of Jensen's inequality
(`StrictConvex.ae_eq_const_or_average_mem_interior`) it would equal `M` on the whole ball, which
contains maximum points farther away than `z`.

## Main declarations

* `TauCeti.exists_mem_frontier_isMaxOn_of_le_setAverage_ball`: a continuous function with the
  sub-mean-value property on balls at the interior points of a compact set attains its maximum
  on the frontier.
* `TauCeti.le_of_le_setAverage_ball_le_frontier`, `TauCeti.ge_of_setAverage_ball_le_ge_frontier`:
  the weak maximum and minimum principles for the sub- and super-mean-value properties.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.3, Theorem 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {u : E → ℝ}

/-- **Maximum principle for the sub-mean-value property.** Let `K` be a nonempty compact set
and let `u` be continuous on `K`. If at every interior point `x` of `K` the value `u x` is at
most the average of `u` over `ball x r` for arbitrarily small radii `r > 0`, then `u` attains its
maximum over `K` at a point of `frontier K`. -/
theorem exists_mem_frontier_isMaxOn_of_le_setAverage_ball {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hu : ContinuousOn u K)
    (hsub : ∀ x ∈ interior K, ∃ᶠ r in 𝓝[>] 0, u x ≤ ⨍ y in ball x r, u y ∂μ) :
    ∃ x ∈ frontier K, IsMaxOn u K x := by
  obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMaxOn hne hu
  -- The maximum points of `u` on `K` form a compact set; take one, `z`, farthest from `z₀`.
  have hA : IsCompact (K ∩ u ⁻¹' {u z₀}) :=
    hK.of_isClosed_subset (hu.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  obtain ⟨z, ⟨hzK, hzM⟩, hzfar⟩ :=
    hA.exists_isMaxOn ⟨z₀, hz₀K, rfl⟩ (continuous_id.dist continuous_const).continuousOn
  refine ⟨z, ?_, fun y hy ↦ (hzM ▸ hz₀ hy :)⟩
  rw [hK.isClosed.frontier_eq]
  refine ⟨hzK, fun hzint ↦ ?_⟩
  -- If `z` were interior, the sub-mean-value property would hold on a ball `ball z r ⊆ K`.
  obtain ⟨ε, hε, hεK⟩ := nhds_basis_closedBall.mem_iff.1 (mem_interior_iff_mem_nhds.1 hzint)
  obtain ⟨r, hmean, hr, hrε⟩ := ((hsub z hzint).and_eventually (Ioo_mem_nhdsGT hε)).exists
  have hrK : closedBall z r ⊆ K := (closedBall_subset_closedBall hrε.le).trans hεK
  have hle : ∀ y ∈ ball z r, u y ≤ u z := fun y hy ↦ hzM ▸ hz₀ (hrK (ball_subset_closedBall hy))
  -- By the equality case of Jensen's inequality, `u` is constant on that ball, since it is
  -- bounded above by `u z` there and its average is at least `u z`.
  have : IsFiniteMeasure (μ.restrict (ball z r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hcont : ContinuousOn u (ball z r) := hu.mono (ball_subset_closedBall.trans hrK)
  obtain hae | havg := (strictConvex_Iic (u z)).ae_eq_const_or_average_mem_interior isClosed_Iic
    ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hle))
    (((hu.mono hrK).integrableOn_compact (μ := μ) (isCompact_closedBall z r)).mono_set
      ball_subset_closedBall)
  swap
  · rw [interior_Iic] at havg
    exact (not_le.2 havg hmean).elim
  have hball := Measure.eqOn_open_of_ae_eq hae isOpen_ball hcont continuousOn_const
  -- That ball contains maximum points farther from `z₀` than `z`, a contradiction.
  have hfr : z ∈ frontier (closedBall z₀ (dist z z₀))ᶜ := by
    rw [frontier_compl, frontier_closedBall' z₀ (dist z z₀)]
    exact mem_sphere.2 rfl
  obtain ⟨y, hy, hyz⟩ := Metric.mem_closure_iff.1 (frontier_subset_closure hfr) r hr
  have hyr : y ∈ ball z r := mem_ball'.2 hyz
  have hyM : u y = u z₀ := hzM ▸ le_antisymm (hle y hyr) (hmean.trans (hball hyr).ge)
  exact hy (mem_closedBall.2 (hzfar ⟨hrK (ball_subset_closedBall hyr), hyM⟩))

/-- **Weak maximum principle for the sub-mean-value property.** Let `K` be compact and let `u` be
continuous on `K`. If at every interior point `x` of `K` the value `u x` is at most the average of
`u` over `ball x r` for arbitrarily small radii `r > 0`, then any bound `m` that `u` respects on
`frontier K` bounds `u` on all of `K`. -/
theorem le_of_le_setAverage_ball_le_frontier {K : Set E} (hK : IsCompact K) {m : ℝ}
    (hu : ContinuousOn u K)
    (hsub : ∀ x ∈ interior K, ∃ᶠ r in 𝓝[>] 0, u x ≤ ⨍ y in ball x r, u y ∂μ)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → u x ≤ m) : ∀ ⦃x⦄, x ∈ K → u x ≤ m := by
  intro x hx
  obtain ⟨z, hz, hzmax⟩ := exists_mem_frontier_isMaxOn_of_le_setAverage_ball hK ⟨x, hx⟩ hu hsub
  exact (hzmax hx).trans (hbdry hz)

/-- **Weak minimum principle for the super-mean-value property.** Let `K` be compact and let `u`
be continuous on `K`. If at every interior point `x` of `K` the value `u x` is at least the average
of `u` over `ball x r` for arbitrarily small radii `r > 0`, then any lower bound `m` that `u`
respects on `frontier K` bounds `u` from below on all of `K`. -/
theorem ge_of_setAverage_ball_le_ge_frontier {K : Set E} (hK : IsCompact K) {m : ℝ}
    (hu : ContinuousOn u K)
    (hsup : ∀ x ∈ interior K, ∃ᶠ r in 𝓝[>] 0, ⨍ y in ball x r, u y ∂μ ≤ u x)
    (hbdry : ∀ ⦃x⦄, x ∈ frontier K → m ≤ u x) : ∀ ⦃x⦄, x ∈ K → m ≤ u x := by
  intro x hx
  have h := le_of_le_setAverage_ball_le_frontier (u := -u) (m := -m) hK hu.neg
    (fun y hy ↦ (hsup y hy).mono fun r hr ↦ by simpa [average_neg] using hr)
    (fun y hy ↦ neg_le_neg (hbdry hy)) hx
  simpa using h

end TauCeti
