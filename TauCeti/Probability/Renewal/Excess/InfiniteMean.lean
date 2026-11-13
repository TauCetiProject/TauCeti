/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import TauCeti.Probability.Renewal.Excess.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Support
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf
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
  let hT_ae (n : ℕ) : AEMeasurable (T n) P := (hid n).aemeasurable_fst
  let T' : ℕ → Ω → ℝ≥0 := fun n ↦ (hT_ae n).mk (T n)
  have hT' (n : ℕ) : Measurable (T' n) := (hT_ae n).measurable_mk
  have hae (n : ℕ) : T n =ᵐ[P] T' n := (hT_ae n).ae_eq_mk
  have hindep' : iIndepFun T' P := hindep.congr hae
  have hid' (n : ℕ) : IdentDistrib (T' n) (T' 0) P P :=
    (hT_ae n).identDistrib_mk.symm.trans ((hid n).trans (hT_ae 0).identDistrib_mk)
  have hmap : P.map (T' 0) = P.map (T 0) := (Measure.map_congr (hae 0)).symm
  have hmean' : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T' 0)) = ∞ := hmap ▸ hmean
  have hF := (P.map (T' 0)).measure_singleton_lt_one_of_lintegral_pos
    (f := fun u ↦ (u : ℝ≥0∞)) (a := 0) (by simp) (hmean' ▸ ENNReal.zero_lt_top)
  have hzero' : P {ω | T' 0 ω = 0} < 1 := by
    rwa [Measure.map_apply (hT' 0) (measurableSet_singleton 0)] at hF
  have hlim' := tendsto_measureReal_renewalExcess_le_of_tendsto_renewalFunction_sub
    hT' hindep' hid' hzero' x
    ((P.map (T' 0)).tendsto_renewalFunction_add_sub_of_mean_eq_top hmean' x)
  have hcongr (t : ℝ≥0) :
      P.real {ω | renewalExcess T' t ω ≤ x} = P.real {ω | renewalExcess T t ω ≤ x} := by
    apply measureReal_congr
    filter_upwards [renewalExcess_congr_ae hae] with ω hω
    simp [hω t]
  simpa only [hcongr] using hlim'

/-- For i.i.d. nonnegative increments of infinite extended mean, lattice or nonlattice, the
probability that the excess exceeds any fixed threshold `x` tends to one as `t → ∞`. -/
theorem tendsto_measureReal_lt_renewalExcess_of_mean_eq_top
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂P.map (T 0)) = ∞) (x : ℝ≥0) :
    Tendsto (fun t ↦ P.real {ω | x < renewalExcess T t ω}) atTop (𝓝 1) := by
  have := hindep.isProbabilityMeasure
  have he (t : ℝ≥0) : P.real {ω | x < renewalExcess T t ω} =
      1 - P.real {ω | renewalExcess T t ω ≤ x} := by
    have hnull : NullMeasurableSet {ω | renewalExcess T t ω ≤ x} P :=
      (aemeasurable_renewalExcess (fun n ↦ (hid n).aemeasurable_fst) t).nullMeasurableSet_preimage
        measurableSet_Iic
    rw [← probReal_compl_eq_one_sub₀ hnull]
    congr 1
    ext ω
    simp
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
  have hae (t : ℝ≥0) : AEMeasurable (fun ω ↦ (renewalExcess T t ω : ℝ)) P :=
    measurable_coe_nnreal_real.comp_aemeasurable
      (aemeasurable_renewalExcess (fun n ↦ (hid n).aemeasurable_fst) t)
  simp_rw [Measure.cdf_map P _ (hae _)]
  by_cases hx : 0 ≤ x
  · have he (t : ℝ≥0) : (fun ω ↦ (renewalExcess T t ω : ℝ)) ⁻¹' Iic x =
        {ω | renewalExcess T t ω ≤ x.toNNReal} := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_ofPred_eq, ← NNReal.coe_le_coe,
        Real.coe_toNNReal x hx]
    simp_rw [he]
    exact tendsto_measureReal_renewalExcess_le_of_mean_eq_top hindep hid hmean x.toNNReal
  · have hempty (t : ℝ≥0) : (fun ω ↦ (renewalExcess T t ω : ℝ)) ⁻¹' Iic x = ∅ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le_of_gt ((lt_of_not_ge hx).trans_le (renewalExcess T t ω).coe_nonneg)
    simp_rw [hempty, measureReal_empty]
    exact tendsto_const_nhds

end TauCeti.Probability
