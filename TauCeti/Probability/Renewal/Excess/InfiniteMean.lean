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
import TauCeti.Probability.Renewal.InfiniteMean

/-!
# Excess-life escape for infinite-mean renewal processes

For independent, identically distributed nonnegative increments of infinite extended mean —
whether lattice or nonlattice — the excess life `E t = renewalExcess T t` escapes every bounded
interval in probability as `t → ∞`:

```text
P(E t ≤ x) ⟶ 0,     P(x < E t) ⟶ 1.
```

Equivalently, the cumulative distribution function of the real-valued excess tends pointwise to
zero at every real threshold.

The argument combines the pathwise inclusion `{E t ≤ x} ⊆ {N t < N (t + x)}`, which bounds
`P(E t ≤ x)` by `(m (t + x)).toReal - (m t).toReal`, with vanishing fixed-window renewal
increments in both the lattice and nonlattice Blackwell regimes. Neither strict measurability of
the increments (beyond the almost-everywhere measurability carried by `IdentDistrib`) nor a
separate `P(T 0 = 0) < 1` hypothesis is needed, and atoms at zero are permitted.

## Main statements

* `TauCeti.Probability.tendsto_measureReal_renewalExcess_le_of_mean_eq_top`: unconditional
  infinite-mean excess escape `P(E t ≤ x) → 0` for every `x : ℝ≥0`.
* `TauCeti.Probability.tendsto_measureReal_lt_renewalExcess_of_mean_eq_top`: complementary tail
  limit `P(x < E t) → 1` for every `x : ℝ≥0`.
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

/-- **Infinite-mean excess escape.** For i.i.d. nonnegative increments of infinite extended mean,
lattice or nonlattice, the probability that the excess at time `t` is at most `x` tends to zero
as `t → ∞` through all nonnegative real observation times. Zero increments are permitted. -/
theorem tendsto_measureReal_renewalExcess_le_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | renewalExcess T t ω ≤ x}) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  exact tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub hindep hid
    ((P.map (T 0)).measure_singleton_zero_lt_one_of_mean_eq_top hmean) x
    ((P.map (T 0)).tendsto_renewalFunction_add_sub_of_mean_eq_top hmean x)

/-- For i.i.d. nonnegative increments of infinite extended mean, lattice or nonlattice, the
probability that the excess exceeds any fixed threshold `x` tends to one as `t → ∞`. -/
theorem tendsto_measureReal_lt_renewalExcess_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop (𝓝 1) := by
  have := hindep.isProbabilityMeasure
  have he (t : ℝ≥0) : P.real {ω | x < renewalExcess T t ω} =
      1 - P.real {ω | renewalExcess T t ω ≤ x} := by
    linarith [measureReal_renewalExcess_le_eq_one_sub (fun n ↦ (hid n).aemeasurable_fst) t x]
  simp_rw [he]
  simpa using tendsto_const_nhds.sub
    (tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x)

/-- For i.i.d. nonnegative increments of infinite extended mean, lattice or nonlattice, the
cumulative distribution function of the real-valued excess tends pointwise to zero at every real
threshold `x`. -/
theorem tendsto_cdf_renewalExcess_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ) :
    Tendsto (fun t ↦ cdf (P.map (fun ω ↦ (renewalExcess T t ω : ℝ))) x) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hT (n : ℕ) : AEMeasurable (T n) P := (hid n).aemeasurable_fst
  have hae (t : ℝ≥0) : AEMeasurable (fun ω ↦ (renewalExcess T t ω : ℝ)) P := by fun_prop
  simp_rw [Measure.cdf_map P _ (hae _), measureReal_preimage_coe_renewalExcess_Iic]
  split_ifs
  · exact tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x.toNNReal
  · exact tendsto_const_nhds

end TauCeti.Probability
