/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Excess.Basic
import TauCeti.MeasureTheory.Measure.AEMeasurable
import TauCeti.Probability.IdentDistrib
import TauCeti.Probability.Independence.Basic

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

variable [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- For an almost surely nonexplosive process with integrable counts at both endpoints,
the measure of the event of an excess at most `x` is bounded by the integral of the count increment.
Independence and identical distribution of increments are not required. -/
theorem measureReal_renewalExcess_le_le_integral_sub
    (hT : ∀ n, AEMeasurable (T n) P)
    (hne : ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop)
    (t x : ℝ≥0)
    (ht : Integrable (fun ω ↦ (renewalCountNat T t ω : ℝ)) P)
    (htx : Integrable (fun ω ↦ (renewalCountNat T (t + x) ω : ℝ)) P) :
    P.real {ω | renewalExcess T t ω ≤ x} ≤
      (∫ ω, (renewalCountNat T (t + x) ω : ℝ) ∂P) -
        ∫ ω, (renewalCountNat T t ω : ℝ) ∂P := by
  have hs : NullMeasurableSet {ω | renewalExcess T t ω ≤ x} P :=
    nullMeasurableSet_le (aemeasurable_renewalExcess hT t) aemeasurable_const
  have hind : P.real {ω | renewalExcess T t ω ≤ x} =
      ∫ ω, {ω | renewalExcess T t ω ≤ x}.indicator (fun _ ↦ (1 : ℝ)) ω ∂P := by
    rw [integral_indicator₀ hs, setIntegral_const, smul_eq_mul, mul_one]
  rw [hind, ← integral_sub htx ht]
  refine integral_mono_ae ((integrable_const (1 : ℝ)).indicator₀ hs) (htx.sub ht) ?_
  filter_upwards [hne] with ω hω
  have hmono : (renewalCountNat T t ω : ℝ) ≤ renewalCountNat T (t + x) ω :=
    Nat.cast_le.mpr (monotone_renewalCountNat T ω le_self_add)
  by_cases hx : renewalExcess T t ω ≤ x
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte]
    have hlt := (renewalExcess_le_iff_renewalCountNat_lt hω).1 hx
    have hle : (renewalCountNat T t ω : ℝ) + 1 ≤ renewalCountNat T (t + x) ω := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    linarith
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte]
    linarith

omit [IsFiniteMeasure P] in
/-- The excess distribution function is bounded by the renewal-function increment.
The bound applies also to infinite-mean interarrival laws and to laws with an atom at zero. -/
theorem measureReal_renewalExcess_le_le_renewalFunction_sub
    (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (t x : ℝ≥0) :
    P.real {ω | renewalExcess T t ω ≤ x} ≤
      ((P.map (T 0)).renewalFunction (t + x)).toReal -
        ((P.map (T 0)).renewalFunction t).toReal := by
  have := hindep.isProbabilityMeasure
  let T' : ℕ → Ω → ℝ≥0 := fun n ↦ (hid n).aemeasurable_fst.mk (T n)
  have hT' (n : ℕ) : Measurable (T' n) := (hid n).aemeasurable_fst.measurable_mk
  have hindep' : iIndepFun T' P := hindep.aemeasurable_mk fun n ↦ (hid n).aemeasurable_fst
  have hid' (n : ℕ) : IdentDistrib (T' n) (T' 0) P P := (hid n).aemeasurable_mk
  have hzero' : P {ω | T' 0 ω = 0} < 1 :=
    ((hid 0).aemeasurable_fst.measure_setOf_mk (· = 0)).trans_lt hzero
  have heq : P.real {ω | renewalExcess T t ω ≤ x} = P.real {ω | renewalExcess T' t ω ≤ x} := by
    refine measureReal_congr (eventuallyEqSet_iff.2 ?_)
    filter_upwards [renewalExcess_congr_ae (T' := T')
      fun n ↦ (hid n).aemeasurable_fst.ae_eq_mk] with ω hω
    simp [hω t]
  have hint (s : ℝ≥0) : Integrable (fun ω ↦ (renewalCountNat T' s ω : ℝ)) P :=
    (integrable_toReal_renewalCount hT' hindep' hid' hzero' s).congr <| by
      filter_upwards [ae_natCast_renewalCountNat hindep' hid' hzero'] with ω hω
      rw [← hω s, ENNReal.toReal_natCast]
  rw [heq, ← (hid 0).aemeasurable_fst.map_mk]
  simpa only [integral_renewalCountNat hT' hindep' hid' hzero'] using
    measureReal_renewalExcess_le_le_integral_sub (fun n ↦ (hT' n).aemeasurable)
      (ae_tendsto_arrival_atTop hindep' hid' hzero') t x (hint t) (hint (t + x))

end TauCeti.Probability
