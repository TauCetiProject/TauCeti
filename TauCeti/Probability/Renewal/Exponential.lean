/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Count
public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Distributions.Gamma.Sum
public import TauCeti.Probability.Distributions.Poisson.Basic
public import TauCeti.Probability.Distributions.Poisson.SizeBias
public import TauCeti.Probability.Distributions.Poisson.Tail

/-!
# Renewal processes with exponential increments

Let the increments `T 0, T 1, …` of a renewal process be independent with the exponential law of
rate `r`. Then the `n`-th arrival time has the gamma (Erlang) law of shape `n` and rate `r`,
and the count `N t` of arrivals in `[0, t]` has the Poisson law of mean `r * t`. Consequently the
renewal function is linear, `𝔼[N t] = r * t`.

The count law follows from the duality between gamma and Poisson laws. For `n ≥ 1`,
`n ≤ N t` holds exactly when the `n`-th arrival is at most `t`, so `P(n ≤ N t)` is the gamma cdf
`P(n, r * t)`, the regularized lower incomplete gamma function. This is also the mass that the
Poisson law of mean `r * t` gives to `{k | n ≤ k}`, and the upper tails determine a probability
law on `ℕ`. The exponential law has no atom at zero, so the process does not explode and the
natural-valued count `renewalCountNat` agrees almost surely with the extended count.

The increments are real-valued in the hypotheses through their coercions, because Mathlib's
exponential law `ProbabilityTheory.expMeasure` lives on `ℝ`. No separate positivity hypothesis on
the rate `r : ℝ≥0` is needed: `expMeasure 0` is the zero measure, which is not the law of a random
variable on a probability space.

## Main results

* `TauCeti.Probability.hasLaw_arrival_gammaMeasure` — the `n`-th arrival time is
  `Gamma(n, r)`-distributed for `n ≠ 0`.
* `TauCeti.Probability.hasLaw_renewalCountNat_poissonMeasure` — the count at time `t` is
  Poisson with mean `r * t`.
* `TauCeti.Probability.lintegral_renewalCount_of_expMeasure`,
  `TauCeti.Probability.integral_renewalCountNat_of_expMeasure` — the renewal function is
  `t ↦ r * t`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0} {r : ℝ≥0}

/-- **Nonexplosion with exponential increments.** For independent exponential increments,
almost surely the arrival times tend to infinity. -/
theorem ae_tendsto_arrival_atTop_of_expMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop := by
  have := hindep.isProbabilityMeasure
  refine ae_tendsto_arrival_atTop hT hindep (fun n ↦ ?_) ?_
  · simpa [Function.comp_def] using ((hlaw n).identDistrib (hlaw 0)).comp measurable_real_toNNReal
  · refine (measure_mono_null (fun ω hω ↦ ?_)
      (ae_iff.1 (ae_pos_of_hasLaw_expMeasure (hlaw 0)))).trans_lt zero_lt_one
    simp_all

/-- **Erlang arrival times.** For independent exponential increments of rate `r`, the `n`-th
arrival time has the gamma law of shape `n` and rate `r` whenever `n ≠ 0`. -/
theorem hasLaw_arrival_gammaMeasure (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) {n : ℕ} (hn : n ≠ 0) :
    HasLaw (fun ω ↦ (arrival T n ω : ℝ)) (gammaMeasure n r) P := by
  have := hindep.isProbabilityMeasure
  have hr := pos_of_hasLaw_expMeasure (hlaw 0)
  have hindep' : iIndepFun (fun i ω ↦ (T i ω : ℝ)) P :=
    hindep.comp (fun _ x ↦ (x : ℝ)) fun _ ↦ measurable_coe_nnreal_real
  have h := hindep'.hasLaw_sum_gammaMeasure (s := Finset.range n) (a := fun _ ↦ 1)
    (by exact_mod_cast hr) (Finset.nonempty_range_iff.2 hn) (fun _ _ ↦ one_pos)
    (fun i _ ↦ hlaw i)
  simpa [arrival_def] using h

/-- For independent exponential increments of rate `r`, the count at time `t` reaches `n`
with probability `P(n, r * t)`, the regularized lower incomplete gamma function. -/
theorem measure_le_renewalCountNat_of_expMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) {n : ℕ}
    (hn : n ≠ 0) :
    P {ω | n ≤ renewalCountNat T t ω} = ENNReal.ofReal (regularizedGamma n (r * t)) := by
  have := hindep.isProbabilityMeasure
  have hr := pos_of_hasLaw_expMeasure (hlaw 0)
  have hae : {ω | n ≤ renewalCountNat T t ω} =ᵐ[P] {ω | (arrival T n ω : ℝ) ≤ t} := by
    filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hT hindep hlaw] with ω hω
    simp [le_renewalCountNat_iff hω]
  rw [measure_congr hae, ← ofReal_measureReal,
    measureReal_le_of_hasLaw_gammaMeasure (by exact_mod_cast Nat.pos_of_ne_zero hn)
      (by exact_mod_cast hr) (hasLaw_arrival_gammaMeasure hindep hlaw hn)]

/-- **Poisson counts.** For independent exponential increments of rate `r`, the number of
arrivals in `[0, t]` has the Poisson law of mean `r * t`. -/
theorem hasLaw_renewalCountNat_poissonMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) :
    HasLaw (renewalCountNat T t) (poissonMeasure (r * t)) P := by
  have := hindep.isProbabilityMeasure
  have hm := measurable_renewalCountNat hT t
  refine ⟨hm.aemeasurable, Measure.ext_of_Ici _ _ fun n ↦ ?_⟩
  rw [Measure.map_apply hm measurableSet_Ici]
  cases n with
  | zero => simp
  | succ m =>
    have htail : (Ici (m + 1) : Set ℕ) = {k | m < k} := by
      ext k
      simp
    rw [← ofReal_measureReal (μ := poissonMeasure (r * t)), htail,
      poissonMeasure_tail_eq_regularizedGamma, ← htail, NNReal.coe_mul, ← Nat.cast_succ,
      ← measure_le_renewalCountNat_of_expMeasure hT hindep hlaw t m.succ_ne_zero]
    simp [preimage]

/-- For independent exponential increments of rate `r`, the count at time `t` equals `n` with
the Poisson probability `exp (-(r * t)) * (r * t) ^ n / n!`. -/
theorem measureReal_renewalCountNat_eq_of_expMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) (n : ℕ) :
    P.real {ω | renewalCountNat T t ω = n} =
      Real.exp (-(r * t)) * (r * t) ^ n / n.factorial := by
  rw [(hasLaw_renewalCountNat_poissonMeasure hT hindep hlaw t).measureReal_eq
    (p := fun k ↦ k = n) .of_discrete, ofPred_eq_eq_singleton, poissonMeasure_real_singleton]
  simp

/-- **The renewal function of exponential increments.** For independent exponential increments of
rate `r`, the expected number of arrivals in `[0, t]` is `r * t`. -/
theorem lintegral_renewalCount_of_expMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) :
    ∫⁻ ω, renewalCount T t ω ∂P = r * t := by
  have hae : ∀ᵐ ω ∂P, (renewalCountNat T t ω : ℝ≥0∞) = renewalCount T t ω := by
    filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hT hindep hlaw] with ω hω
    exact natCast_renewalCountNat hω t
  rw [← lintegral_congr_ae hae,
    (hasLaw_renewalCountNat_poissonMeasure hT hindep hlaw t).lintegral_comp
      (f := fun k : ℕ ↦ (k : ℝ≥0∞)) .of_discrete,
    lintegral_natCast_poissonMeasure]
  simp

/-- The real-valued form of `TauCeti.Probability.lintegral_renewalCount_of_expMeasure`: the
natural-valued count at time `t` has mean `r * t`. -/
theorem integral_renewalCountNat_of_expMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) (t : ℝ≥0) :
    ∫ ω, (renewalCountNat T t ω : ℝ) ∂P = r * t := by
  rw [← Function.comp_def (fun k : ℕ ↦ (k : ℝ)),
    (hasLaw_renewalCountNat_poissonMeasure hT hindep hlaw t).integral_comp
      .of_discrete,
    integral_natCast_poissonMeasure]
  simp

end TauCeti.Probability
