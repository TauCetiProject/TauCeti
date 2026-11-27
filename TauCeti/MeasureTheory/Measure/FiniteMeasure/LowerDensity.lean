/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.MeasureTheory.Measure.Portmanteau
import TauCeti.MeasureTheory.Covering.HausdorffDensity
import TauCeti.MeasureTheory.Measure.LowerDensity
import TauCeti.Topology.MetricSpace.Closeds

/-!
# Lower density bounds in weak limits of finite measures

Let finite measures `μ i` converge weakly to `ν`, and let closed sets `Z i` converge to `Z₀` in
the Hausdorff distance. Suppose that, uniformly in `i`, the measure `μ i` of each closed ball
centred at a point of `Z i` with radius `ρ ∈ [h i, ρ₀]` is at least `c ρ ^ d`, where the
smallest admissible radius `h i` tends to zero. Then the limit measure satisfies the same bound
at every point of `Z₀` and every radius `ρ ∈ (0, ρ₀]`
(`MeasureTheory.FiniteMeasure.le_measure_closedBall_of_tendsto`). Indeed, a point `x ∈ Z₀` is
eventually within `ρ - ρ'` of some point `y ∈ Z i`, so `closedBall y ρ' ⊆ closedBall x ρ`, and the
portmanteau theorem bounds the limit superior of the masses of the closed set `closedBall x ρ` by
its mass for `ν`; finally `ρ' → ρ`. This argument, with the limit superior bound on the ball as a
hypothesis and only the points of `Z i` near `x` used, is
`MeasureTheory.Measure.le_measure_closedBall_of_limsup_le` in
`TauCeti.MeasureTheory.Measure.LowerDensity`; it also serves for vague limits of locally finite
measures.

Combined with the density comparison for Hausdorff measure
(`MeasureTheory.Measure.mul_hausdorffMeasure_le_measure_of_isOpen`), this bounds the
`d`-dimensional Hausdorff measure of the limit set by the limit measure:
`(c / 2 ^ d) μH[d] Z₀ ≤ ν U` for every open `U ⊇ Z₀`
(`MeasureTheory.FiniteMeasure.mul_hausdorffMeasure_le_measure_of_tendsto`). In particular `Z₀` has
finite `d`-dimensional Hausdorff measure when `c > 0`
(`MeasureTheory.FiniteMeasure.hausdorffMeasure_lt_top_of_tendsto`).

This is how a monotonicity estimate valid down to a vanishing scale, such as Taubes's lower bound
for the defect energy of balls about the zeros of large-parameter Seiberg–Witten solutions, yields
a lower density bound for the limit measure and finite Hausdorff measure of the limit set.

## References

* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 6.9.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Filter Metric Set TopologicalSpace Topology
open scoped ENNReal

namespace MeasureTheory.FiniteMeasure

variable {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {l : Filter ι} {μ : ι → FiniteMeasure X} {ν : FiniteMeasure X} {Z : ι → Closeds X}
  {Z₀ : Closeds X} {h : ι → ℝ} {c ρ₀ : ℝ} {d : ℕ}

/-- **Lower density bounds pass to weak limits.** Let finite measures `μ i` converge weakly to
`ν` and closed sets `Z i` converge to `Z₀` in the Hausdorff distance along a nontrivial filter, and
let `h i → 0`. If eventually `c ρ ^ d ≤ μ i (closedBall y ρ)` for every `y ∈ Z i` and every
radius `h i ≤ ρ ≤ ρ₀`, then `c ρ ^ d ≤ ν (closedBall x ρ)` for every `x ∈ Z₀` and every radius
`0 < ρ ≤ ρ₀`. -/
theorem le_measure_closedBall_of_tendsto [l.NeBot] (hμ : Tendsto μ l (𝓝 ν))
    (hZ : Tendsto Z l (𝓝 Z₀)) (hh : Tendsto h l (𝓝 0))
    (hdens : ∀ᶠ i in l, ∀ y ∈ Z i, ∀ ρ, h i ≤ ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ d) ≤ (μ i : Measure X) (closedBall y ρ))
    {x : X} (hx : x ∈ Z₀) {ρ : ℝ} (hρ : 0 < ρ) (hρρ₀ : ρ ≤ ρ₀) :
    ENNReal.ofReal (c * ρ ^ d) ≤ (ν : Measure X) (closedBall x ρ) :=
  -- The portmanteau theorem bounds the limit superior on the closed ball by its `ν`-mass.
  Measure.le_measure_closedBall_of_limsup_le
    (fun _ hε ↦ hZ.isKuratowskiLimit.eventually_exists_dist_lt hx hε)
    hh univ_mem (hdens.mono fun _ hi y hy ↦ hi y hy.1) hρ hρρ₀
    (limsup_measure_closed_le_of_tendsto hμ isClosed_closedBall)

variable [BorelSpace X]

/-- **Hausdorff measure of a limit set.** Under the hypotheses of
`MeasureTheory.FiniteMeasure.le_measure_closedBall_of_tendsto`, with `ρ₀ > 0`, the limit measure
dominates `c / 2 ^ d` times the `d`-dimensional Hausdorff measure of the limit set:
`(c / 2 ^ d) μH[d] Z₀ ≤ ν U` for every open set `U` containing `Z₀`. -/
theorem mul_hausdorffMeasure_le_measure_of_tendsto [l.NeBot] (hμ : Tendsto μ l (𝓝 ν))
    (hZ : Tendsto Z l (𝓝 Z₀)) (hh : Tendsto h l (𝓝 0)) (hρ₀ : 0 < ρ₀)
    (hdens : ∀ᶠ i in l, ∀ y ∈ Z i, ∀ ρ, h i ≤ ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ d) ≤ (μ i : Measure X) (closedBall y ρ))
    {U : Set X} (hU : IsOpen U) (hZU : (Z₀ : Set X) ⊆ U) :
    ENNReal.ofReal (c / 2 ^ d) * μH[d] (Z₀ : Set X) ≤ (ν : Measure X) U :=
  Measure.mul_hausdorffMeasure_le_measure_of_isOpen _ hU hZU fun _ hx ↦
    Measure.frequently_ofReal_div_mul_rpow_le_measure_closedBall <| Eventually.frequently <|
      eventually_of_mem (Ioc_mem_nhdsGT hρ₀) fun _ hρ ↦
        le_measure_closedBall_of_tendsto hμ hZ hh hdens hx hρ.1 hρ.2

/-- **The limit set has finite Hausdorff measure.** Under the hypotheses of
`MeasureTheory.FiniteMeasure.le_measure_closedBall_of_tendsto`, with `c > 0` and `ρ₀ > 0`, the
limit set `Z₀` has finite `d`-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_lt_top_of_tendsto [l.NeBot] (hμ : Tendsto μ l (𝓝 ν))
    (hZ : Tendsto Z l (𝓝 Z₀)) (hh : Tendsto h l (𝓝 0)) (hc : 0 < c) (hρ₀ : 0 < ρ₀)
    (hdens : ∀ᶠ i in l, ∀ y ∈ Z i, ∀ ρ, h i ≤ ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ d) ≤ (μ i : Measure X) (closedBall y ρ)) :
    μH[d] (Z₀ : Set X) < ∞ :=
  ENNReal.lt_top_of_mul_ne_top_right
    ((mul_hausdorffMeasure_le_measure_of_tendsto hμ hZ hh hρ₀ hdens isOpen_univ
      (subset_univ _)).trans_lt (measure_lt_top _ _)).ne
    (ENNReal.ofReal_pos.2 (by positivity)).ne'

end MeasureTheory.FiniteMeasure
