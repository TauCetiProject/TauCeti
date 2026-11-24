/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Vague
public import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.MeasureTheory.Measure.LowerDensity

/-!
# Lower density bounds in vague limits of locally finite measures

Let locally finite measures `μs i` on a proper metric space converge vaguely to `μ`, that is
`∫ f ∂μs i → ∫ f ∂μ` for every continuous compactly supported `f`, and let `Z i` be sets. Suppose
that near a point `x`, the measure `μs i` of each closed ball centred at a point of `Z i` with
radius `ρ ∈ [h i, ρ₀]` is at least `c ρ ^ d`, where the smallest admissible radius `h i` tends to
zero. If `x` is a limit of points of `Z i`, then the limit measure satisfies the same bound at
`x` for every radius `ρ ∈ (0, ρ₀]`
(`MeasureTheory.Measure.le_measure_closedBall_of_tendsto_integral_compactlySupported`). This is the
counterpart for locally finite measures of
`MeasureTheory.FiniteMeasure.le_measure_closedBall_of_tendsto`: the portmanteau inequality on
closed sets is replaced by its form for the compact closed balls
(`MeasureTheory.Measure.limsup_measure_le_of_tendsto_integral_compactlySupported`), and only the
points of `Z i` near `x` and the convergence of points to `x` are used, rather than Hausdorff
convergence of the sets.

Neither the measures nor the sets need be bounded, and the bound need only hold near `x`, with
constants that may vary from point to point. This is the setting of a noncompact manifold or of
the total space of a vector bundle. When the constants can be chosen uniformly near each point of
a set of such limits, the density comparison for Hausdorff measure
(`MeasureTheory.Measure.isLocallyFiniteMeasure_restrict_hausdorffMeasure_of_ofReal_mul_pow_le`)
shows that this set has locally finite `d`-dimensional Hausdorff measure.

This is how a monotonicity estimate valid down to a vanishing scale, such as Taubes's lower bound
for the defect energy of balls about the zeros of large-parameter Seiberg–Witten solutions, yields
the lower density of a vague limit of the defect measures, and with it the local finiteness of
the Hausdorff measure of the limit zero set.

## References

* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Chapter 1 (weak convergence
  of Radon measures) and Theorem 6.9.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Filter Metric Set Topology
open scoped ENNReal CompactlySupported

namespace MeasureTheory.Measure

variable {X ι : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  {l : Filter ι} {μs : ι → Measure X} {μ : Measure X}
  [∀ i, IsLocallyFiniteMeasure (μs i)] [IsLocallyFiniteMeasure μ]
  {Z : ι → Set X} {h : ι → ℝ} {d : ℕ}

/-- **Lower density bounds pass to vague limits.** Let locally finite measures `μs i` converge
vaguely to `μ` along a nontrivial filter, let `h i → 0`, and let `x` be a limit of points of
`Z i`: for every `ε > 0`, eventually some point of `Z i` lies within `ε` of `x`. If, for some
neighbourhood `U` of `x`, eventually `c ρ ^ d ≤ μs i (closedBall y ρ)` for every `y ∈ Z i ∩ U` and
every radius `h i ≤ ρ ≤ ρ₀`, then `c ρ ^ d ≤ μ (closedBall x ρ)` for every radius
`0 < ρ ≤ ρ₀`. -/
theorem le_measure_closedBall_of_tendsto_integral_compactlySupported [l.NeBot]
    (hμ : ∀ f : C_c(X, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ)))
    {x : X} (hx : ∀ ε > 0, ∀ᶠ i in l, ∃ y ∈ Z i, dist y x < ε) (hh : Tendsto h l (𝓝 0))
    {U : Set X} (hU : U ∈ 𝓝 x) {c ρ₀ : ℝ}
    (hdens : ∀ᶠ i in l, ∀ y ∈ Z i ∩ U, ∀ ρ, h i ≤ ρ → ρ ≤ ρ₀ →
      ENNReal.ofReal (c * ρ ^ d) ≤ μs i (closedBall y ρ))
    {ρ : ℝ} (hρ : 0 < ρ) (hρρ₀ : ρ ≤ ρ₀) :
    ENNReal.ofReal (c * ρ ^ d) ≤ μ (closedBall x ρ) :=
  -- The portmanteau inequality on the compact closed ball bounds the limit superior.
  le_measure_closedBall_of_limsup_le hx hh hU hdens hρ hρρ₀
    (limsup_measure_le_of_tendsto_integral_compactlySupported hμ (isCompact_closedBall x ρ))

end MeasureTheory.Measure
