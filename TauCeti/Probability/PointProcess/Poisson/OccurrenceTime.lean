/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.PointProcess.OccurrenceTime.Basic
public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Distributions.Poisson.Tail
public import Mathlib.Probability.Distributions.Exponential

/-!
# Erlang occurrence times of a homogeneous Poisson random measure

For intensity `r • nnvolume`, with `r > 0`, occurrence `n` (indexed from zero)
has the Gamma law of shape `n + 1` and rate `r`. The first occurrence therefore
has the exponential law. All occurrence times are simultaneously positive and
finite almost surely.

The extended-valued law retains the possible value infinity until the law itself
rules it out. No pathwise local finiteness or integrality assumption is needed:
finite Poisson counts on each tested window suffice for the threshold identity.
These marginal laws are ingredients of the interarrival description; they do not
assert independence of the gaps.

The occurrence-time cumulative mass is a Poisson tail, equal to the regularized
lower incomplete Gamma function, as in the scalar identities of
`TauCeti.Probability.Distributions.Poisson.Tail` and
`TauCeti.Probability.Distributions.Gamma.Cdf`.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge
  University Press, 2018, Chapter 7.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {N : Ω → Measure ℝ≥0} {r : ℝ≥0}

/-- The probability that occurrence `n` has happened by time `t` is the Gamma
cumulative mass of shape `n + 1`, including the endpoint `t`. -/
theorem IsPoissonRandomMeasure.measureReal_occurrenceTime_le
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (n : ℕ) (t : ℝ≥0) :
    P.real {ω | (N ω).occurrenceTime n ≤ t} =
      regularizedGamma (n + 1) ((r : ℝ) * t) := by
  have hcount (s : ℝ≥0) : HasLaw (fun ω => N ω (Iic s))
      ((poissonMeasure (r * s)).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
    simpa only [smul_apply, smul_eq_mul, nnvolume_Iic,
      ← ENNReal.coe_mul, ENNReal.toNNReal_coe] using
      h.hasLaw (A := Iic s) measurableSet_Iic (by
        simp only [smul_apply, smul_eq_mul, nnvolume_Iic]
        finiteness)
  have hfinite : ∀ᵐ ω ∂P, N ω (Iic (t + 1)) ≠ ∞ :=
    (h.ae_lt_top measurableSet_Iic (by
      simp only [smul_apply, smul_eq_mul, nnvolume_Iic]
      finiteness)).mono fun _ hω => hω.ne
  have hevent : {ω | (N ω).occurrenceTime n ≤ t} =ᵐ[P]
      {ω | (n + 1 : ℝ≥0∞) ≤ N ω (Iic t)} := by
    filter_upwards [hfinite] with ω hω
    exact (N ω).occurrenceTime_le_iff_of_measure_Iic_ne_top n t ⟨t + 1, lt_add_one t, hω⟩
  rw [measureReal_congr hevent,
    (hcount t).measureReal_eq (p := fun x : ℝ≥0∞ => (n + 1 : ℝ≥0∞) ≤ x)
      measurableSet_Ici,
    measureReal_def, Measure.map_apply (f := (Nat.cast : ℕ → ℝ≥0∞))
      (s := {x | (n + 1 : ℝ≥0∞) ≤ x}) Measurable.of_discrete measurableSet_Ici]
  have hpre : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' {x | (n + 1 : ℝ≥0∞) ≤ x} =
      {k | n < k} := by
    ext k
    simp only [mem_preimage, mem_ofPred_eq]
    norm_cast
  rw [hpre]
  exact (poissonMeasure_tail_eq_regularizedGamma (r * t) n).trans (by simp)

/-- Occurrence `n` of a positive-rate homogeneous Poisson random measure has the
Erlang law, as an extended nonnegative variable. Index zero is the first occurrence,
not an artificial occurrence at the origin. -/
theorem IsPoissonRandomMeasure.hasLaw_occurrenceTime
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω => (N ω).occurrenceTime n)
      ((gammaMeasure (n + 1) r).map ENNReal.ofReal) P := by
  let := h.isProbabilityMeasure
  have hr' : 0 < (r : ℝ) := hr
  have hn : 0 < (n + 1 : ℝ) := by positivity
  let := isProbabilityMeasure_gammaMeasure hn hr'
  refine ⟨((Measure.measurable_occurrenceTime n).comp h.measurable).aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro t
  induction t using ENNReal.recTopCoe with
  | top => simp
  | coe t =>
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
      Measure.map_apply (by fun_prop) measurableSet_Iic]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    have hpre : ENNReal.ofReal ⁻¹' Iic (t : ℝ≥0∞) = Iic (t : ℝ) := by
      ext x
      simp only [mem_preimage, mem_Iic, ENNReal.ofReal_le_coe]
    rw [hpre]
    exact (h.measureReal_occurrenceTime_le n t).trans
      (measureReal_Iic_gammaMeasure hn hr' t).symm

/-- Every occurrence of a positive-rate homogeneous Poisson random measure is
strictly after zero and finite, on one event of probability one. -/
theorem IsPoissonRandomMeasure.ae_forall_occurrenceTime_pos_lt_top
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ n, 0 < (N ω).occurrenceTime n ∧ (N ω).occurrenceTime n < ∞ := by
  rw [ae_all_iff]
  intro n
  apply ((h.hasLaw_occurrenceTime hr n).ae_iff
    (p := fun x => 0 < x ∧ x < ∞)
    (measurableSet_setOfPred.1 (measurableSet_Ioi.inter measurableSet_Iio))).2
  apply (ae_map_iff (f := ENNReal.ofReal) (by fun_prop)
    (p := fun x => 0 < x ∧ x < ∞)
    (measurableSet_Ioi.inter measurableSet_Iio)).2
  filter_upwards [ae_pos_gammaMeasure (n + 1) r] with x hx
  simp [ENNReal.ofReal_pos.mpr hx]

/-- The real-valued version of occurrence `n` has Gamma shape `n + 1` and rate `r`.
The exceptional value assigned by `toReal` at infinity does not affect this law. -/
theorem IsPoissonRandomMeasure.hasLaw_toReal_occurrenceTime
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω => ((N ω).occurrenceTime n).toReal) (gammaMeasure (n + 1) r) P := by
  have hm := (hasLaw_map (P := (gammaMeasure (n + 1) r).map ENNReal.ofReal)
    (X := ENNReal.toReal) ENNReal.measurable_toReal.aemeasurable).fun_comp
      (h.hasLaw_occurrenceTime hr n)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hm
  have heq : (gammaMeasure (n + 1) r).map (ENNReal.toReal ∘ ENNReal.ofReal) =
      gammaMeasure (n + 1) r := by
    calc
      _ = (gammaMeasure (n + 1) r).map id := by
        apply Measure.map_congr
        filter_upwards [ae_pos_gammaMeasure (n + 1) r] with x hx
        exact ENNReal.toReal_ofReal hx.le
      _ = _ := Measure.map_id
  simpa only [heq] using hm

/-- The first occurrence of a positive-rate homogeneous Poisson random measure has
the exponential law. -/
theorem IsPoissonRandomMeasure.hasLaw_toReal_occurrenceTime_zero
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω => ((N ω).occurrenceTime 0).toReal) (expMeasure r) P := by
  simpa only [Nat.cast_zero, zero_add, expMeasure] using
    h.hasLaw_toReal_occurrenceTime hr 0

end TauCeti.Probability
