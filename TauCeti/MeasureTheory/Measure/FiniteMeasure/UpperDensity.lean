/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import TauCeti.MeasureTheory.Covering.HausdorffDensity

/-!
# Upper density bounds in weak limits of finite measures

Let finite measures `μ i` converge weakly to `ν`. Suppose that, at a point `x`, the measure
`μ i` of each closed ball centred at `x` with radius `ρ ∈ [h i, ρ₀]` is at most `c ρ ^ d`, where
the smallest admissible radius `h i` tends to zero. Then the limit measure satisfies the same
bound at every radius `ρ ∈ [0, ρ₀)`
(`MeasureTheory.FiniteMeasure.measure_closedBall_le_of_tendsto`).
Indeed, for `ρ < ρ' ≤ ρ₀` a bounded continuous function `φ` with `1` on `closedBall x ρ` and
`0` outside `closedBall x ρ'` gives `ν (closedBall x ρ) ≤ ∫ φ dν = lim ∫ φ dμ i ≤ c ρ' ^ d`;
finally `ρ' → ρ`. When `0 < d`, the bound at `ρ = 0` says that `ν` has no atom at `x`.

Combined with the comparison of upper densities with Hausdorff measure
(`MeasureTheory.Measure.measure_le_mul_hausdorffMeasure`), a uniform upper bound at every point of
a set `A` bounds the limit measure of `A` by `c` times its `d`-dimensional Hausdorff measure:
`ν A ≤ c μH[d] A` (`MeasureTheory.FiniteMeasure.measure_le_mul_hausdorffMeasure_of_tendsto`).

This is the counterpart of `TauCeti.MeasureTheory.Measure.FiniteMeasure.LowerDensity`. A
monotonicity estimate valid down to a vanishing scale, such as Taubes's quadratic upper bound for
the defect energy of balls for large-parameter Seiberg–Witten solutions, thus yields an upper
density bound for the limit measure, and together with the lower bound it makes the limit measure
comparable with the Hausdorff measure of the limit set.

## References

* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 6.9.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory.FiniteMeasure

variable {X ι : Type*} [MeasurableSpace X] {l : Filter ι} {h : ι → ℝ} {c ρ₀ : ℝ} {d : ℕ}

section PseudoMetricSpace

variable [PseudoMetricSpace X] [OpensMeasurableSpace X] {μ : ι → FiniteMeasure X}
  {ν : FiniteMeasure X}

/-- **Closed balls in a weak limit.** Let finite measures `μ i` converge weakly to `ν` along a
nontrivial filter, and let `ρ < ρ'`. If eventually `μ i (closedBall x ρ') ≤ b`, then
`ν (closedBall x ρ) ≤ b`. -/
theorem measure_closedBall_le_of_tendsto_of_lt [l.NeBot] (hμ : Tendsto μ l (𝓝 ν)) {x : X}
    {ρ ρ' : ℝ} (hρρ' : ρ < ρ') {b : ℝ≥0∞}
    (hb : ∀ᶠ i in l, (μ i : Measure X) (closedBall x ρ') ≤ b) :
    (ν : Measure X) (closedBall x ρ) ≤ b := by
  have hδ : 0 < ρ' - ρ := sub_pos.2 hρρ'
  -- The test function `φ` is `1` on `closedBall x ρ` and vanishes outside `closedBall x ρ'`.
  set φ := thickenedIndicator hδ (closedBall x ρ)
  have hφ : ∀ (m : Measure X), ∫⁻ y, (φ y : ℝ≥0∞) ∂m ≤ m (closedBall x ρ') := by
    intro m
    rw [← lintegral_indicator_one measurableSet_closedBall]
    refine lintegral_mono fun y ↦ ?_
    by_cases hy : y ∈ closedBall x ρ'
    · rw [indicator_of_mem hy, Pi.one_apply, ENNReal.coe_le_one_iff]
      exact thickenedIndicator_le_one hδ _ y
    · rw [thickenedIndicator_zero hδ _ fun hy' ↦ hy ?_, ENNReal.coe_zero]
      · exact bot_le
      obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy'
      rw [mem_closedBall] at hz ⊢
      linarith [dist_triangle y z x]
  have hlim := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.1 hμ φ
  calc (ν : Measure X) (closedBall x ρ) ≤ ∫⁻ y, (φ y : ℝ≥0∞) ∂(ν : Measure X) :=
        measure_le_lintegral_thickenedIndicator _ measurableSet_closedBall hδ
    _ ≤ b := le_of_tendsto hlim (hb.mono fun i hi ↦ (hφ _).trans hi)

/-- **Upper density bounds pass to weak limits.** Let finite measures `μ i` converge weakly to
`ν` along a nontrivial filter, and let `h i → 0`. If eventually
`μ i (closedBall x ρ) ≤ c ρ ^ d` for every radius `h i ≤ ρ ≤ ρ₀`, then
`ν (closedBall x ρ) ≤ c ρ ^ d` for every radius `0 ≤ ρ < ρ₀`. -/
theorem measure_closedBall_le_of_tendsto [l.NeBot] (hμ : Tendsto μ l (𝓝 ν))
    (hh : Tendsto h l (𝓝 0)) {x : X}
    (hdens : ∀ᶠ i in l, ∀ ρ, h i ≤ ρ → ρ ≤ ρ₀ →
      (μ i : Measure X) (closedBall x ρ) ≤ ENNReal.ofReal (c * ρ ^ d))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρρ₀ : ρ < ρ₀) :
    (ν : Measure X) (closedBall x ρ) ≤ ENNReal.ofReal (c * ρ ^ d) := by
  -- It suffices to prove the bound with `c ρ' ^ d` for every `ρ' ∈ (ρ, ρ₀)`, and let `ρ' → ρ`.
  have hcont : Tendsto (fun ρ' : ℝ ↦ ENNReal.ofReal (c * ρ' ^ d)) (𝓝[>] ρ)
      (𝓝 (ENNReal.ofReal (c * ρ ^ d))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow d))).tendsto ρ).mono_left
      nhdsWithin_le_nhds
  refine ge_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT hρρ₀] with ρ' hρ'
  refine measure_closedBall_le_of_tendsto_of_lt hμ hρ'.1 ?_
  filter_upwards [hdens, hh.eventually (gt_mem_nhds (hρ.trans_lt hρ'.1))] with i hi hhi
  exact hi ρ' hhi.le hρ'.2.le

end PseudoMetricSpace

variable [MetricSpace X] [BorelSpace X] {μ : ι → FiniteMeasure X} {ν : FiniteMeasure X}

/-- **Hausdorff measure bounds a limit measure.** Under the hypotheses of
`MeasureTheory.FiniteMeasure.measure_closedBall_le_of_tendsto` at every point of a set `A`, with
`c > 0` and `ρ₀ > 0`, the limit measure of `A` is at most `c` times its `d`-dimensional Hausdorff
measure: `ν A ≤ c μH[d] A`. -/
theorem measure_le_mul_hausdorffMeasure_of_tendsto [l.NeBot] (hμ : Tendsto μ l (𝓝 ν))
    (hh : Tendsto h l (𝓝 0)) (hc : 0 < c) (hρ₀ : 0 < ρ₀) {A : Set X}
    (hdens : ∀ x ∈ A, ∀ᶠ i in l, ∀ ρ, h i ≤ ρ → ρ ≤ ρ₀ →
      (μ i : Measure X) (closedBall x ρ) ≤ ENNReal.ofReal (c * ρ ^ d)) :
    (ν : Measure X) A ≤ ENNReal.ofReal c * μH[d] A := by
  have h2 : (2 : ℝ≥0∞) ^ (d : ℝ) ≠ 0 := by simp
  have h2' : (2 : ℝ≥0∞) ^ (d : ℝ) ≠ ∞ := by simp
  have hc' : ENNReal.ofReal c / 2 ^ (d : ℝ) ≠ 0 :=
    ENNReal.div_ne_zero.2 ⟨ENNReal.ofReal_pos.2 hc |>.ne', h2'⟩
  have key := Measure.measure_le_mul_hausdorffMeasure (ν : Measure X) (d := d) hc'
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top h2) (A := A) fun x hx ↦ ?_
  · rwa [ENNReal.mul_div_cancel h2 h2'] at key
  filter_upwards [Ioo_mem_nhdsGT hρ₀] with ρ hρ
  have hrw : ENNReal.ofReal c / 2 ^ (d : ℝ) * ENNReal.ofReal (2 * ρ) ^ (d : ℝ) =
      ENNReal.ofReal (c * ρ ^ d) := by
    -- Normalize coercions and powers, then cancel the factor `2 ^ d`.
    simp only [ENNReal.rpow_natCast, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_mul hc.le, ENNReal.ofReal_pow hρ.1.le, mul_pow]
    rw [← mul_assoc, ENNReal.div_mul_cancel (by simp) (by simp)]
  rw [hrw]
  exact measure_closedBall_le_of_tendsto hμ hh (hdens x hx) hρ.1.le hρ.2

end MeasureTheory.FiniteMeasure
