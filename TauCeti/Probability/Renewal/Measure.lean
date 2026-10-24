/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.ConvolutionPower
public import TauCeti.Probability.Renewal.Moments

/-!
# The renewal measure and the renewal function

Let `F` be a measure on an additive monoid, typically the law of the nonnegative increments of a
renewal process. Its *renewal measure* is the sum of its convolution powers

```text
U = ∑ n, F^{*n} = δ₀ + F + F * F + ⋯,
```

where `F^{*0} = δ₀`. It satisfies the renewal equation `U = δ₀ + F * U`. On the time axis `ℝ≥0`
the *renewal function* is `m t = (F * U) [0, t] = ∑_{n ≥ 1} F^{*n} [0, t]`, so that
`U [0, t] = 1 + m t`; the term `δ₀` accounts for the artificial arrival at time zero, while an atom
of `F` at zero contributes genuine arrivals at time zero to `m 0`.

For a renewal process with independent increments of common law `F`, the `n`-th arrival time has
law `F^{*n}`, and the expected number of arrivals in `[0, t]` is the renewal function:
`𝔼 (renewalCount T t) = m t`. In particular `m` depends only on the law `F`. The renewal function
is always nondecreasing. When `F` is a probability measure with `F {0} < 1`, the finite moments of
the renewal counts show that `m t` is finite, so `U` is finite on compact sets, and `m` is
right-continuous.

The renewal measure is the central object of the renewal equation `g = h + g * F` and of the
renewal limit theorems, which describe `m t / t` and `U [t, t + h]` as `t → ∞`.

## Main definitions

* `MeasureTheory.Measure.renewalMeasure` — the sum `∑ n, F^{*n}` of the convolution powers.
* `MeasureTheory.Measure.renewalFunction` — the renewal function `m t = (F * U) [0, t]`.

## Main results

* `MeasureTheory.Measure.renewalMeasure_eq_dirac_add_conv` — the renewal equation
  `U = δ₀ + F * U`.
* `MeasureTheory.Measure.renewalFunction_eq_tsum` — `m t = ∑_{n ≥ 1} F^{*n} [0, t]`.
* `MeasureTheory.Measure.renewalMeasure_Iic` — `U [0, t] = 1 + m t`.
* `TauCeti.Probability.hasLaw_arrival` — the `n`-th arrival time has law `F^{*n}`.
* `TauCeti.Probability.lintegral_renewalCount` — `𝔼 (renewalCount T t) = m t`.
* `MeasureTheory.Measure.renewalFunction_lt_top`,
  `MeasureTheory.Measure.isFiniteMeasureOnCompacts_renewalMeasure` — finiteness of `m` and of `U`
  on compact sets when `F {0} < 1`.
* `MeasureTheory.Measure.continuousWithinAt_renewalFunction_Ici` — right continuity of `m`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal MeasureTheory

namespace MeasureTheory.Measure

/-! ### The renewal measure -/

section RenewalMeasure

variable {α : Type*} [MeasurableSpace α] [AddMonoid α] (F : Measure α)

/-- The renewal measure `∑ n, F^{*n}` of a measure `F`: the sum of all its convolution powers,
including the point mass `F^{*0} = δ₀` at zero. -/
def renewalMeasure : Measure α :=
  Measure.sum F.convolutionPower

lemma renewalMeasure_def : F.renewalMeasure = Measure.sum F.convolutionPower := (rfl)

lemma renewalMeasure_apply (s : Set α) : F.renewalMeasure s = ∑' n, F.convolutionPower n s := by
  rw [renewalMeasure_def, sum_apply_of_countable]

instance sfinite_renewalMeasure [SFinite F] : SFinite F.renewalMeasure := by
  rw [renewalMeasure_def]
  infer_instance

/-- Every convolution power of `F` is dominated by its renewal measure. -/
lemma convolutionPower_le_renewalMeasure (n : ℕ) : F.convolutionPower n ≤ F.renewalMeasure :=
  le_sum _ n

variable [MeasurableAdd₂ α] [SFinite F]

/-- Convolving the renewal measure with `F` removes the term `F^{*0} = δ₀`:
`F * U = ∑ n, F^{*(n + 1)}`. -/
lemma conv_renewalMeasure :
    F ∗ F.renewalMeasure = Measure.sum fun n ↦ F.convolutionPower (n + 1) := by
  simp_rw [renewalMeasure_def, conv_sum, convolutionPower_succ']

/-- **The renewal equation.** The renewal measure satisfies `U = δ₀ + F * U`. -/
theorem renewalMeasure_eq_dirac_add_conv :
    F.renewalMeasure = dirac 0 + F ∗ F.renewalMeasure := by
  ext s hs
  rw [conv_renewalMeasure, add_apply, sum_apply _ hs, renewalMeasure_apply,
    tsum_eq_zero_add' ENNReal.summable, convolutionPower_zero]

end RenewalMeasure

/-! ### The renewal function -/

section RenewalFunction

variable (F : Measure ℝ≥0)

/-- The renewal function `m t = (F * U) [0, t]` of a measure `F` on the time axis `ℝ≥0`, where
`U` is the renewal measure. It equals `∑_{n ≥ 1} F^{*n} [0, t]` (`renewalFunction_eq_tsum`) and,
for a renewal process with increments of law `F`, the expected number of arrivals in `[0, t]`
(`TauCeti.Probability.lintegral_renewalCount`). -/
def renewalFunction (t : ℝ≥0) : ℝ≥0∞ :=
  (F ∗ F.renewalMeasure) (Iic t)

lemma renewalFunction_def (t : ℝ≥0) : F.renewalFunction t = (F ∗ F.renewalMeasure) (Iic t) :=
  (rfl)

/-- The renewal function is nondecreasing. -/
lemma monotone_renewalFunction : Monotone F.renewalFunction :=
  fun _ _ hst ↦ measure_mono (Iic_subset_Iic.2 hst)

variable [SFinite F]

lemma renewalFunction_eq_tsum (t : ℝ≥0) :
    F.renewalFunction t = ∑' n, F.convolutionPower (n + 1) (Iic t) := by
  rw [renewalFunction_def, conv_renewalMeasure, sum_apply_of_countable]

/-- The renewal measure of `[0, t]` counts the artificial arrival at time zero in addition to the
renewal function: `U [0, t] = 1 + m t`. -/
theorem renewalMeasure_Iic (t : ℝ≥0) : F.renewalMeasure (Iic t) = 1 + F.renewalFunction t := by
  conv_lhs => rw [renewalMeasure_eq_dirac_add_conv]
  rw [add_apply, dirac_apply_of_mem (by simp : (0 : ℝ≥0) ∈ Iic t), renewalFunction_def]

end RenewalFunction

end MeasureTheory.Measure

/-! ### Laws of the arrival times and the expected count -/

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- For independent increments with common law `F = P.map (T 0)`, the `n`-th arrival time
`arrival T n` has law the convolution power `F^{*n}`. -/
theorem hasLaw_arrival (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (n : ℕ) : HasLaw (arrival T n) ((P.map (T 0)).convolutionPower n) P := by
  have := hindep.isProbabilityMeasure
  have hsum : arrival T n = ∑ i ∈ Finset.range n, T i := by
    ext ω
    simp [arrival_def]
  simpa [hsum] using
    hindep.hasLaw_finset_sum_convolutionPower (fun i ↦ ⟨(hid i).aemeasurable_fst, (hid i).map_eq⟩)
      (Finset.range n)

/-- **The expected renewal count.** For independent increments with common law `F = P.map (T 0)`,
the expected number of arrivals in `[0, t]` is the renewal function `m t`. In particular it depends
only on `F`. No assumption on `F` is needed: both sides may be infinite. -/
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

/-! ### Finiteness and right continuity -/

namespace MeasureTheory.Measure

open TauCeti.Probability

variable {F : Measure ℝ≥0} [IsProbabilityMeasure F]

/-- **Finiteness of the renewal function.** If `F` is a probability measure on `ℝ≥0` that is not
the point mass at zero, i.e. `F {0} < 1`, then `m t < ∞` for every `t`. No assumption is made on
the mean of `F`. -/
theorem renewalFunction_lt_top (hF : F {0} < 1) (t : ℝ≥0) : F.renewalFunction t < ∞ := by
  -- Realize i.i.d. increments of law `F` as the coordinates of the product space.
  set P : Measure (ℕ → ℝ≥0) := Measure.infinitePi fun _ ↦ F
  have hP (n : ℕ) : MeasurePreserving (fun w : ℕ → ℝ≥0 ↦ w n) P F :=
    measurePreserving_eval_infinitePi _ n
  have hindep : iIndepFun (fun n (w : ℕ → ℝ≥0) ↦ w n) P :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) fun _ ↦ measurable_id
  have hid (n : ℕ) : IdentDistrib (fun w : ℕ → ℝ≥0 ↦ w n) (fun w ↦ w 0) P P :=
    ⟨(hP n).measurable.aemeasurable, (hP 0).measurable.aemeasurable, by
      rw [(hP n).map_eq, (hP 0).map_eq]⟩
  have hzero : P {w | w 0 = 0} < 1 := by
    rwa [show {w : ℕ → ℝ≥0 | w 0 = 0} = (fun w ↦ w 0) ⁻¹' {0} from rfl,
      (hP 0).measure_preimage (measurableSet_singleton 0).nullMeasurableSet]
  rw [← (hP 0).map_eq, ← lintegral_renewalCount hindep hid t]
  simpa using lintegral_renewalCount_pow_lt_top (fun n ↦ (hP n).measurable) hindep hid hzero t 1

/-- If `F {0} < 1`, the renewal measure of every interval `[0, t]` is finite. -/
theorem renewalMeasure_Iic_lt_top (hF : F {0} < 1) (t : ℝ≥0) : F.renewalMeasure (Iic t) < ∞ := by
  rw [renewalMeasure_Iic]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, renewalFunction_lt_top hF t⟩

/-- If `F {0} < 1`, the renewal measure is finite on compact sets: it is a locally finite measure
on `ℝ≥0`. -/
theorem isFiniteMeasureOnCompacts_renewalMeasure (hF : F {0} < 1) :
    IsFiniteMeasureOnCompacts F.renewalMeasure where
  lt_top_of_isCompact K hK := by
    obtain ⟨t, ht⟩ := hK.bddAbove
    exact (measure_mono fun _ hx ↦ ht hx).trans_lt (renewalMeasure_Iic_lt_top hF t)

/-- **Right continuity of the renewal function.** If `F {0} < 1`, then `m` is right-continuous. -/
theorem continuousWithinAt_renewalFunction_Ici (hF : F {0} < 1) (t : ℝ≥0) :
    ContinuousWithinAt F.renewalFunction (Ici t) t := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have hI : ⋂ r > t, Iic r = Iic t := by
    ext x
    simp only [mem_iInter, mem_Iic]
    exact ⟨fun h ↦ le_of_forall_gt_imp_ge_of_dense h, fun h r hr ↦ h.trans hr.le⟩
  have := tendsto_measure_biInter_gt (μ := F ∗ F.renewalMeasure) (s := Iic) (a := t)
    (fun _ _ ↦ measurableSet_Iic.nullMeasurableSet) (fun _ _ _ hij ↦ Iic_subset_Iic.2 hij)
    ⟨t + 1, lt_add_one t, (renewalFunction_lt_top hF (t + 1)).ne⟩
  rwa [hI] at this

end MeasureTheory.Measure
