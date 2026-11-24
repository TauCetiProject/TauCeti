/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import TauCeti.Probability.Renewal.Excess.Basic
import TauCeti.Probability.Cdf
import TauCeti.Probability.Renewal.Excess.Escape

/-!
# Excess-life distribution functions for infinite-mean renewal processes

For independent, identically distributed nonnegative increments of infinite extended mean —
whether lattice or nonlattice — the excess life `E t = renewalExcess T t` escapes every bounded
interval in probability as `t → ∞`
(`TauCeti.Probability.tendsto_measureReal_renewalExcess_le_of_mean_eq_top` in
`TauCeti.Probability.Renewal.Excess.Escape`). Equivalently, the cumulative distribution
function of the real-valued excess tends pointwise to zero at every real threshold. Neither strict
measurability of the increments (beyond the almost-everywhere measurability carried by
`IdentDistrib`) nor a separate `P(T 0 = 0) < 1` hypothesis is needed, and atoms at zero are
permitted.

## Main statements

* `TauCeti.Probability.tendsto_cdf_renewalExcess_of_mean_eq_top`: pointwise vanishing of the CDF
  of the real-valued excess at every `x : ℝ`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §4.
* Vincent Tassion, *Applied Stochastic Processes*, lecture notes, ETH Zürich, 2025, Chapter 6.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- For i.i.d. nonnegative increments of infinite extended mean, lattice or nonlattice, the
cumulative distribution function of the real-valued excess tends pointwise to zero at every real
threshold `x`. -/
theorem tendsto_cdf_renewalExcess_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hT (n : ℕ) : AEMeasurable (T n) P := (hid n).aemeasurable_fst
  simp_rw [Measure.cdf_map_coe_nnreal P (aemeasurable_renewalExcess hT _)]
  split_ifs
  · exact tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x.toNNReal
  · exact tendsto_const_nhds

end TauCeti.Probability
