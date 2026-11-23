/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Basic

/-!
# Bounding excess life by renewal increments

On a nonexplosive path, the excess at time `t` is at most `x` exactly when the count
increases between `t` and `t + x`. The increment counts arrivals in `(t, t + x]`, so
arrivals exactly at the upper endpoint are included, whereas arrivals at `t` are not.
This remains valid when several arrivals coincide and when there are arrivals at zero.

Taking expectations bounds the excess distribution function by `m(t + x) - m(t)`.
Thus vanishing renewal increments imply that the excess escapes every bounded interval;
no finite-mean assumption is needed for this bound.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Wiley, 1971, Chapter XI.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} {T : ℕ → Ω → ℝ≥0}

/-- The next arrival is within `x` of `t` exactly when the count increases by time `t + x`.
This includes an arrival exactly at `t + x`, even in the presence of zero increments. -/
lemma renewalExcess_le_iff_renewalCountNat_lt {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) {t x : ℝ≥0} :
    renewalExcess T t ω ≤ x ↔ renewalCountNat T t ω < renewalCountNat T (t + x) ω := by
  rw [← Nat.succ_le_iff, le_renewalCountNat_iff hω, ← add_renewalExcess hω t]
  exact (add_le_add_iff_left t).symm

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- For an almost surely nonexplosive process, the measure of `{renewalExcess T t ≤ x}` plus the
extended expected count at time `t` is bounded by the extended expected count at `t + x`. Neither
finiteness of `P`, independence, nor identical distribution is required. -/
theorem measure_renewalExcess_le_add_lintegral_renewalCount_le {t x : ℝ≥0}
    (hnull : NullMeasurableSet {ω | renewalExcess T t ω ≤ x} P)
    (hne : ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop) :
    P {ω | renewalExcess T t ω ≤ x} + ∫⁻ ω, renewalCount T t ω ∂P ≤
      ∫⁻ ω, renewalCount T (t + x) ω ∂P := by
  rw [← lintegral_indicator_one₀ hnull,
    ← lintegral_add_left' (f := {ω | renewalExcess T t ω ≤ x}.indicator 1)
      (aemeasurable_const.indicator₀ hnull)]
  refine lintegral_mono_ae ?_
  filter_upwards [hne] with ω hω
  rw [← natCast_renewalCountNat hω t, ← natCast_renewalCountNat hω (t + x)]
  by_cases hx : renewalExcess T t ω ≤ x
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte, Pi.one_apply]
    rw [add_comm]
    exact_mod_cast Nat.succ_le_of_lt ((renewalExcess_le_iff_renewalCountNat_lt hω).1 hx)
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte, zero_add]
    exact_mod_cast monotone_renewalCountNat T ω le_self_add

/-- For an almost surely nonexplosive process with integrable counts at both endpoints,
the measure of the event of an excess at most `x` is bounded by the integral of the count increment.
Independence, identical distribution, strict increment measurability, and finiteness of `P` are not
required. -/
theorem measureReal_renewalExcess_le_le_integral_sub
    (hne : ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop)
    (t x : ℝ≥0)
    (ht : Integrable (fun ω ↦ (renewalCountNat T t ω : ℝ)) P)
    (htx : Integrable (fun ω ↦ (renewalCountNat T (t + x) ω : ℝ)) P) :
    P.real {ω | renewalExcess T t ω ≤ x} ≤
      (∫ ω, (renewalCountNat T (t + x) ω : ℝ) ∂P) -
        ∫ ω, (renewalCountNat T t ω : ℝ) ∂P := by
  have hnull : NullMeasurableSet {ω | renewalExcess T t ω ≤ x} P := by
    refine ((htx.sub ht).aemeasurable.nullMeasurableSet_preimage
      (measurableSet_Ioi (a := (0 : ℝ)))).congr ?_
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hne] with ω hω
    simp [renewalExcess_le_iff_renewalCountNat_lt hω, sub_pos]
  have hle := measure_renewalExcess_le_add_lintegral_renewalCount_le hnull hne
  have hlint (s : ℝ≥0) (hs : Integrable (fun ω ↦ (renewalCountNat T s ω : ℝ)) P) :
      ∫⁻ ω, renewalCount T s ω ∂P =
        ENNReal.ofReal (∫ ω, (renewalCountNat T s ω : ℝ) ∂P) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)
        hs.aestronglyMeasurable, ENNReal.ofReal_toReal]
    · refine lintegral_congr_ae ?_
      filter_upwards [hne] with ω hω
      rw [← natCast_renewalCountNat hω s, ENNReal.ofReal_natCast]
    · refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_) hs.hasFiniteIntegral)
      filter_upwards with ω
      rw [Real.eNorm_eq_ofReal (Nat.cast_nonneg _)]
  rw [hlint t ht, hlint (t + x) htx] at hle
  have hPfin : P {ω | renewalExcess T t ω ≤ x} ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hle)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_add hPfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Nat.cast_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Nat.cast_nonneg _),
    ← measureReal_def] at hreal
  linarith

/-- For i.i.d. nonnegative increments with `(P.map (T 0)) {0} < 1`, the excess distribution
function is bounded by the renewal-function increment. The bound applies also to infinite-mean
interarrival laws, laws with an atom at zero, and almost-everywhere measurable increments. -/
theorem measureReal_renewalExcess_le_le_renewalFunction_sub
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : (P.map (T 0)) {0} < 1) (t x : ℝ≥0) :
    P.real {ω | renewalExcess T t ω ≤ x} ≤
      ((P.map (T 0)).renewalFunction (t + x)).toReal -
        ((P.map (T 0)).renewalFunction t).toReal := by
  have := hindep.isProbabilityMeasure
  have hzero' : P {ω | T 0 ω = 0} < 1 := by
    rwa [Measure.map_apply_of_aemeasurable (hid 0).aemeasurable_fst (measurableSet_singleton 0)]
      at hzero
  have hnull : NullMeasurableSet {ω | renewalExcess T t ω ≤ x} P :=
    (aemeasurable_renewalExcess (fun n ↦ (hid n).aemeasurable_fst) t).nullMeasurableSet_preimage
      measurableSet_Iic
  have hle := measure_renewalExcess_le_add_lintegral_renewalCount_le hnull
    (ae_tendsto_arrival_atTop hindep hid hzero')
  rw [lintegral_renewalCount hindep hid t, lintegral_renewalCount hindep hid (t + x)] at hle
  have hfin : (P.map (T 0)).renewalFunction (t + x) ≠ ∞ :=
    ((P.map (T 0)).renewalFunction_lt_top hzero (t + x)).ne
  have hfin' : (P.map (T 0)).renewalFunction t ≠ ∞ :=
    ((P.map (T 0)).renewalFunction_lt_top hzero t).ne
  have hreal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add (measure_ne_top P _) hfin'] at hreal
  rw [measureReal_def]
  linarith

end TauCeti.Probability
