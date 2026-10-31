/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Moments

/-!
# The renewal measure and the renewal function

For a measure `F` on an additive monoid, the renewal measure is the sum of its convolution powers,

```text
U = ∑ n, F^{∗n} = δ₀ + F + F ∗ F + ⋯,
```

where `F^{∗0} = δ₀` is `Measure.convolutionPower F 0`. It satisfies the renewal equation
`U = δ₀ + F ∗ U`. When `F` is the law of the increments of a renewal process, `F^{∗n}` is the law
of the `n`-th arrival time, so `U s` is the expected number of arrival times in `s`, counting the
artificial arrival at time zero. This file proves that identity for the intervals `[0, t]`.

On the half-line `ℝ≥0`, the renewal function is `m t = (F ∗ U) [0, t] = ∑_{n ≥ 1} F^{∗n} [0, t]`.
For independent increments with law `F`, it is the expected count `𝔼[N t]` of the renewal process,
and `U [0, t] = 1 + m t`; this holds also when `F` has an atom at zero. If `F` is a probability
measure with `F {0} < 1`, the finite moments of the renewal counts show that `m t` is finite. Hence
`U` is finite on bounded intervals, and `m` is nondecreasing and right-continuous. The renewal
measure and the renewal function are the objects of the renewal limit theorems and of the solution
`g = h ∗ U` of the renewal equation `g = h + g ∗ F`.

## Main definitions

* `MeasureTheory.Measure.renewalMeasure` — the renewal measure `∑ n, F^{∗n}`.
* `MeasureTheory.Measure.renewalFunction` — the renewal function `t ↦ (F ∗ U) [0, t]` on `ℝ≥0`.

## Main results

* `MeasureTheory.Measure.renewalMeasure_eq_dirac_add_conv` — the renewal equation
  `U = δ₀ + F ∗ U`.
* `MeasureTheory.Measure.renewalFunction_eq_tsum` — `m t = ∑_{n ≥ 1} F^{∗n} [0, t]`.
* `MeasureTheory.Measure.renewalMeasure_Iic` — `U [0, t] = 1 + m t`.
* `TauCeti.Probability.lintegral_renewalCount` — `𝔼[N t] = m t` for i.i.d. increments.
* `MeasureTheory.Measure.renewalFunction_lt_top`,
  `MeasureTheory.Measure.isLocallyFiniteMeasure_renewalMeasure` — local finiteness when
  `F {0} < 1`.
* `MeasureTheory.Measure.continuousWithinAt_renewalFunction_Ici` — right continuity of `m`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-! ### The renewal measure -/

section RenewalMeasure

variable {α : Type*} [MeasurableSpace α] [AddMonoid α]

/-- The renewal measure `∑ n, μ^{∗n}` of a measure `μ`: the sum of all its convolution powers,
including the point mass `μ^{∗0} = δ₀`. For the law `μ` of the increments of a renewal process,
its mass on `[0, t]` is one more than the expected number of arrivals in `[0, t]`
(`renewalMeasure_Iic` and `TauCeti.Probability.lintegral_renewalCount`). -/
def renewalMeasure (μ : Measure α) : Measure α :=
  Measure.sum μ.convolutionPower

theorem renewalMeasure_def (μ : Measure α) :
    μ.renewalMeasure = Measure.sum μ.convolutionPower := (rfl)

theorem renewalMeasure_apply (μ : Measure α) {s : Set α} (hs : MeasurableSet s) :
    μ.renewalMeasure s = ∑' n, μ.convolutionPower n s := by
  rw [renewalMeasure_def, sum_apply _ hs]

/-- The renewal measure of an s-finite measure is s-finite. -/
instance sfinite_renewalMeasure (μ : Measure α) [SFinite μ] : SFinite μ.renewalMeasure := by
  rw [renewalMeasure_def]
  infer_instance

/-- Convolving the renewal measure with `μ` removes the term `μ^{∗0} = δ₀`:
`μ ∗ U = ∑ n, μ^{∗(n + 1)}`. -/
theorem conv_renewalMeasure [MeasurableAdd₂ α] (μ : Measure α) [SFinite μ] :
    μ ∗ μ.renewalMeasure = Measure.sum fun n ↦ μ.convolutionPower (n + 1) := by
  simp_rw [renewalMeasure_def, conv_sum, convolutionPower_succ']

/-- **The renewal equation** `U = δ₀ + μ ∗ U` for the renewal measure `U` of `μ`. -/
theorem renewalMeasure_eq_dirac_add_conv [MeasurableAdd₂ α] (μ : Measure α) [SFinite μ] :
    μ.renewalMeasure = dirac 0 + μ ∗ μ.renewalMeasure := by
  ext s hs
  rw [conv_renewalMeasure, add_apply, sum_apply _ hs, renewalMeasure_apply _ hs,
    tsum_eq_zero_add' ENNReal.summable, convolutionPower_zero]

end RenewalMeasure

/-! ### The renewal function on the half-line -/

section RenewalFunction

variable (μ : Measure ℝ≥0)

/-- The renewal function `t ↦ (μ ∗ U) [0, t]` of a measure `μ` on `ℝ≥0`, where `U` is the
renewal measure of `μ`. It equals `∑_{n ≥ 1} μ^{∗n} [0, t]` (`renewalFunction_eq_tsum`), and for
independent increments with law `μ` it is the expected count of the renewal process
(`TauCeti.Probability.lintegral_renewalCount`). -/
def renewalFunction (t : ℝ≥0) : ℝ≥0∞ :=
  (μ ∗ μ.renewalMeasure) (Iic t)

theorem renewalFunction_def (t : ℝ≥0) :
    μ.renewalFunction t = (μ ∗ μ.renewalMeasure) (Iic t) := (rfl)

/-- The renewal function is the sum of the masses of `[0, t]` under the positive convolution
powers. -/
theorem renewalFunction_eq_tsum [SFinite μ] (t : ℝ≥0) :
    μ.renewalFunction t = ∑' n, μ.convolutionPower (n + 1) (Iic t) := by
  rw [renewalFunction_def, conv_renewalMeasure, sum_apply _ measurableSet_Iic]

/-- The renewal measure of `[0, t]` is one more than the renewal function at `t`: the extra unit
is the point mass `μ^{∗0} = δ₀`. -/
theorem renewalMeasure_Iic [SFinite μ] (t : ℝ≥0) :
    μ.renewalMeasure (Iic t) = 1 + μ.renewalFunction t := by
  rw [renewalMeasure_eq_dirac_add_conv, add_apply, dirac_apply_of_mem (by simp : (0 : ℝ≥0) ∈ Iic t),
    renewalFunction_def]

/-- The renewal function is nondecreasing in time. -/
theorem monotone_renewalFunction : Monotone μ.renewalFunction :=
  fun _ _ h ↦ measure_mono (Iic_subset_Iic.2 h)

end RenewalFunction

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- **The renewal function is the expected count.** For independent, identically distributed
increments, the expected number of arrivals in `[0, t]` is the renewal function of the common law
of the increments. No assumption is made on the atom of the law at zero, and both sides may be
infinite. -/
theorem lintegral_renewalCount (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (t : ℝ≥0) :
    ∫⁻ ω, renewalCount T t ω ∂P = (P.map (T 0)).renewalFunction t := by
  have := hindep.isProbabilityMeasure
  have hS (n : ℕ) := hasLaw_arrival hindep hid n
  -- The `n`-th term of the series defining the count is the indicator of `{arrival ≤ t}`.
  have hterm (n : ℕ) (ω : Ω) : (if arrival T (n + 1) ω ≤ t then (1 : ℝ≥0∞) else 0) =
      (arrival T (n + 1) ⁻¹' Iic t).indicator (fun _ ↦ 1) ω := by
    by_cases h : arrival T (n + 1) ω ≤ t <;> simp [h]
  have hnull (n : ℕ) : NullMeasurableSet (arrival T (n + 1) ⁻¹' Iic t) P :=
    (hS (n + 1)).aemeasurable.nullMeasurableSet_preimage measurableSet_Iic
  simp only [renewalCount_def, hterm]
  rw [lintegral_tsum fun n ↦ aemeasurable_const.indicator₀ (hnull n),
    Measure.renewalFunction_eq_tsum]
  refine tsum_congr fun n ↦ ?_
  rw [lintegral_indicator_const₀ (hnull n), one_mul, ← (hS (n + 1)).map_eq,
    Measure.map_apply_of_aemeasurable (hS (n + 1)).aemeasurable measurableSet_Iic]

end TauCeti.Probability

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

/-- **The renewal function is finite.** For a probability measure `μ` on `ℝ≥0` that is not the
point mass at zero, the renewal function is finite at every time. No assumption is made on the
mean of `μ`. -/
theorem renewalFunction_lt_top (hμ : μ {0} < 1) (t : ℝ≥0) : μ.renewalFunction t < ∞ := by
  -- Realize i.i.d. increments with law `μ` as the coordinates of the product measure.
  set P := Measure.infinitePi fun _ : ℕ ↦ μ
  have hT : ∀ n, Measurable fun w : ℕ → ℝ≥0 ↦ w n := measurable_pi_apply
  have hindep : iIndepFun (fun n (w : ℕ → ℝ≥0) ↦ w n) P :=
    iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ x ↦ x) fun _ ↦ measurable_id
  have hmap : ∀ n, P.map (fun w ↦ w n) = μ := fun n ↦ infinitePi_map_eval _ n
  have hid : ∀ n, IdentDistrib (fun w : ℕ → ℝ≥0 ↦ w n) (fun w ↦ w 0) P P := fun n ↦
    ⟨(hT n).aemeasurable, (hT 0).aemeasurable, by rw [hmap, hmap]⟩
  have hzero : P {w | w 0 = 0} < 1 := by
    rwa [← hmap 0, map_apply (hT 0) (measurableSet_singleton 0)] at hμ
  rw [← hmap 0, ← TauCeti.Probability.lintegral_renewalCount hindep hid t]
  simpa using TauCeti.Probability.lintegral_renewalCount_pow_lt_top hT hindep hid hzero t 1

/-- The renewal measure of a probability measure on `ℝ≥0` other than the point mass at zero is
finite on every bounded interval `[0, t]`. -/
theorem renewalMeasure_Iic_lt_top (hμ : μ {0} < 1) (t : ℝ≥0) : μ.renewalMeasure (Iic t) < ∞ := by
  rw [renewalMeasure_Iic]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, renewalFunction_lt_top μ hμ t⟩

/-- The renewal measure of a probability measure on `ℝ≥0` other than the point mass at zero is
locally finite. -/
theorem isLocallyFiniteMeasure_renewalMeasure (hμ : μ {0} < 1) :
    IsLocallyFiniteMeasure μ.renewalMeasure :=
  ⟨fun t ↦ ⟨Iic (t + 1), Iic_mem_nhds (lt_add_one t), renewalMeasure_Iic_lt_top μ hμ _⟩⟩

/-- **Right continuity of the renewal function**, for a probability measure on `ℝ≥0` other than
the point mass at zero. -/
theorem continuousWithinAt_renewalFunction_Ici (hμ : μ {0} < 1) (t : ℝ≥0) :
    ContinuousWithinAt μ.renewalFunction (Ici t) t := by
  have hf : μ.renewalFunction = (μ ∗ μ.renewalMeasure) ∘ Iic :=
    funext fun t ↦ renewalFunction_def μ t
  have hinter : ⋂ r > t, Iic r = Iic t := by
    ext x
    simpa using forall_gt_imp_ge_iff_le_of_dense (a₁ := x) (a₂ := t)
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hf, Function.comp_apply, ← hinter]
  refine tendsto_measure_biInter_gt (fun r _ ↦ measurableSet_Iic.nullMeasurableSet)
    (fun _ _ _ h ↦ Iic_subset_Iic.2 h) ⟨t + 1, lt_add_one t, ?_⟩
  exact (renewalFunction_lt_top μ hμ (t + 1)).ne

end MeasureTheory.Measure
