/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Lower density bounds pass to limits of measures

Let measures `μs i` and sets `Z i` be given along a nontrivial filter, and let `x` be a limit of
points of `Z i`. Suppose that near `x`, the measure `μs i` of each closed ball centred at a point
of `Z i` with radius `ρ ∈ [h i, ρ₀]` is at least `c ρ ^ d`, where the smallest admissible radius
`h i` tends to zero. If the limit superior of `μs i (closedBall x ρ)` is at most
`μ (closedBall x ρ)`, then `c ρ ^ d ≤ μ (closedBall x ρ)`
(`MeasureTheory.Measure.le_measure_closedBall_of_limsup_le`). Indeed, `x` is eventually within
`ρ - ρ'` of some point `y ∈ Z i`, so `closedBall y ρ' ⊆ closedBall x ρ`; finally `ρ' → ρ`.

The limit superior bound is the portmanteau inequality for the closed ball, so this one argument
serves both weak limits of finite measures
(`MeasureTheory.FiniteMeasure.le_measure_closedBall_of_tendsto`) and vague limits of locally
finite measures
(`MeasureTheory.Measure.le_measure_closedBall_of_tendsto_integral_compactlySupported`).

## References

* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapter 1 (weak convergence
  of Radon measures and the limit superior bound on compact sets).
-/

public section

open Filter Metric Set Topology
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X ι : Type*} [MetricSpace X] [MeasurableSpace X]

/-- **Lower density bounds pass to limits.** Let `h i → 0` along a nontrivial filter, and let `x`
be a limit of points of `Z i`: for every `ε > 0`, eventually some point of `Z i` lies within `ε`
of `x`. Suppose that, for some neighbourhood `U` of `x`, eventually
`c ρ ^ d ≤ μs i (closedBall y ρ)` for every `y ∈ Z i ∩ U` and every radius `h i ≤ ρ ≤ ρ₀`. If
`0 < ρ ≤ ρ₀` and the limit superior of `μs i (closedBall x ρ)` is at most `μ (closedBall x ρ)`,
then `c ρ ^ d ≤ μ (closedBall x ρ)`. -/
theorem le_measure_closedBall_of_limsup_le {l : Filter ι} [l.NeBot] {μs : ι → Measure X}
    {μ : Measure X} {Z : ι → Set X} {h : ι → ℝ} {d : ℕ} {x : X}
    (hx : ∀ ε > 0, ∀ᶠ i in l, ∃ y ∈ Z i, dist y x < ε) (hh : Tendsto h l (𝓝 0))
    {U : Set X} (hU : U ∈ 𝓝 x) {c ρ₀ : ℝ}
    (hdens : ∀ᶠ i in l, ∀ y ∈ Z i ∩ U, ∀ ρ, h i ≤ ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ d) ≤ μs i (closedBall y ρ))
    {ρ : ℝ} (hρ : 0 < ρ) (hρρ₀ : ρ ≤ ρ₀)
    (hlimsup : limsup (fun i ↦ μs i (closedBall x ρ)) l ≤ μ (closedBall x ρ)) :
    ENNReal.ofReal (c * ρ ^ d) ≤ μ (closedBall x ρ) := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  -- It suffices to prove the bound with `c ρ' ^ d` for every `ρ' ∈ (0, ρ)`, and let `ρ' → ρ`.
  have hcont : Tendsto (fun ρ' : ℝ ↦ ENNReal.ofReal (c * ρ' ^ d)) (𝓝[<] ρ)
      (𝓝 (ENNReal.ofReal (c * ρ ^ d))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow d))).tendsto ρ).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsLT hρ] with ρ' hρ'
  -- Eventually some `y ∈ Z i ∩ U` has `closedBall y ρ' ⊆ closedBall x ρ`, and `h i ≤ ρ'`.
  have hev : ∀ᶠ i in l, ENNReal.ofReal (c * ρ' ^ d) ≤ μs i (closedBall x ρ) := by
    filter_upwards [hdens, hx (min (ρ - ρ') δ) (lt_min (sub_pos.2 hρ'.2) hδ),
      hh.eventually (gt_mem_nhds hρ'.1)] with i hi ⟨y, hy, hyx⟩ hhi
    refine (hi y ⟨hy, hδU (mem_ball.2 (hyx.trans_le (min_le_right _ _)))⟩ ρ' hhi.le
      (hρ'.2.le.trans hρρ₀)).trans (measure_mono fun z hz ↦ ?_)
    rw [mem_closedBall] at hz ⊢
    linarith [dist_triangle z y x, min_le_left (ρ - ρ') δ]
  exact (le_limsup_of_frequently_le hev.frequently).trans hlimsup

end MeasureTheory.Measure
