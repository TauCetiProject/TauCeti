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

variable [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- For an almost surely nonexplosive process with integrable counts at both endpoints,
the measure of the event of an excess at most `x` is bounded by the integral of the count increment.
Independence and identical distribution of increments are not required. -/
theorem measureReal_renewalExcess_le_le_integral_sub
    (hT : ∀ n, Measurable (T n))
    (hne : ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop)
    (t x : ℝ≥0)
    (ht : Integrable (fun ω ↦ (renewalCountNat T t ω : ℝ)) P)
    (htx : Integrable (fun ω ↦ (renewalCountNat T (t + x) ω : ℝ)) P) :
    P.real {ω | renewalExcess T t ω ≤ x} ≤
      (∫ ω, (renewalCountNat T (t + x) ω : ℝ) ∂P) -
        ∫ ω, (renewalCountNat T t ω : ℝ) ∂P := by
  have hs : MeasurableSet {ω | renewalExcess T t ω ≤ x} :=
    measurableSet_le (measurable_renewalExcess hT t) measurable_const
  rw [← integral_indicator_one hs, ← integral_sub htx ht]
  refine integral_mono_ae ((integrable_const (1 : ℝ)).indicator hs) (htx.sub ht) ?_
  filter_upwards [hne] with ω hω
  have hmono : (renewalCountNat T t ω : ℝ) ≤ renewalCountNat T (t + x) ω :=
    Nat.cast_le.mpr (monotone_renewalCountNat T ω le_self_add)
  by_cases hx : renewalExcess T t ω ≤ x
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte, Pi.one_apply]
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
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (t x : ℝ≥0) :
    P.real {ω | renewalExcess T t ω ≤ x} ≤
      ((P.map (T 0)).renewalFunction (t + x)).toReal -
        ((P.map (T 0)).renewalFunction t).toReal := by
  have := hindep.isProbabilityMeasure
  have hint (s : ℝ≥0) : Integrable (fun ω ↦ (renewalCountNat T s ω : ℝ)) P :=
    (integrable_toReal_renewalCount hT hindep hid hzero s).congr <| by
      filter_upwards [ae_natCast_renewalCountNat hindep hid hzero] with ω hω
      rw [← hω s, ENNReal.toReal_natCast]
  simpa only [integral_renewalCountNat hT hindep hid hzero] using
    measureReal_renewalExcess_le_le_integral_sub hT
      (ae_tendsto_arrival_atTop hindep hid hzero) t x (hint t) (hint (t + x))

end TauCeti.Probability
