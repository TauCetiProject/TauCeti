/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable
public import TauCeti.Probability.Finance.BlackScholes.Hedge

/-!
# Predictable Black–Scholes delta hedges

The stock and bond holdings of the Black–Scholes call and put delta hedges are predictable
when evaluated along a continuous adapted positive spot process. The statements use the
existing spot derivative and `TauCeti.BlackScholes.hedgeBondHolding`, on the entire interval
before maturity, and extend each holding by zero at and after maturity. No terminal limit of
the delta is required, including at the strike.

The bond price may be any deterministic Borel function; continuous positive bonds are a
special case. These results supply predictable holdings for stochastic integration. They do
not assert integrability or self-financing.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MeasureTheory.StronglyAdapted

open TauCeti.BlackScholes

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {S : ℝ≥0 → Ω → ℝ} {r σ K T : ℝ}

private theorem measurable_dPlus_process
    (hS : StronglyAdapted ℱ S) (hc : ∀ ω, Continuous (fun t => S t ω)) :
    Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      dPlus (S p.1 p.2) r σ K (T - p.1)) := by
  have hSm : Measurable[ℱ.predictable] (Function.uncurry S) :=
    (hS.isStronglyPredictable_of_continuous hc).measurable
  have htm := (ℱ.measurable_fst_predictable).coe_nnreal_real
  simp only [dPlus_def]
  fun_prop

/-- The call delta along a continuous adapted positive spot process, extended by zero at and
after maturity, is predictable. -/
theorem isStronglyPredictable_deriv_callPrice
    (hS : StronglyAdapted ℱ S) (hc : ∀ ω, Continuous (fun t => S t ω))
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω) (hK : 0 < K) (hσ : σ ≠ 0) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then
      deriv (fun s => callPrice s r σ K (T - t)) (S t ω) else 0) := by
  have htm := (ℱ.measurable_fst_predictable).coe_nnreal_real
  have hd := measurable_dPlus_process (r := r) (σ := σ) (K := K) (T := T) hS hc
  have hh : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ) < T then
      cdf (gaussianReal 0 1) (dPlus (S p.1 p.2) r σ K (T - p.1)) else 0) :=
    ((monotone_cdf (μ := gaussianReal 0 1)).measurable.comp hd).ite
    (measurableSet_lt htm measurable_const) measurable_const
  rw [IsStronglyPredictable]
  convert hh.stronglyMeasurable using 1
  ext p
  simp only [Function.uncurry]
  split_ifs with ht
  · exact deriv_callPrice_spot (r := r) (hpos p.1 p.2 ht) hK hσ (sub_pos.mpr ht)
  · rfl

/-- The put delta along a continuous adapted positive spot process, extended by zero at and
after maturity, is predictable. -/
theorem isStronglyPredictable_deriv_putPrice
    (hS : StronglyAdapted ℱ S) (hc : ∀ ω, Continuous (fun t => S t ω))
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω) (hK : 0 < K) (hσ : σ ≠ 0) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then
      deriv (fun s => putPrice s r σ K (T - t)) (S t ω) else 0) := by
  have htm := (ℱ.measurable_fst_predictable).coe_nnreal_real
  have hd := measurable_dPlus_process (r := r) (σ := σ) (K := K) (T := T) hS hc
  have hh : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ) < T then
      -cdf (gaussianReal 0 1) (-dPlus (S p.1 p.2) r σ K (T - p.1)) else 0) :=
    ((monotone_cdf (μ := gaussianReal 0 1)).measurable.comp hd.neg).neg.ite
    (measurableSet_lt htm measurable_const) measurable_const
  rw [IsStronglyPredictable]
  convert hh.stronglyMeasurable using 1
  ext p
  simp only [Function.uncurry]
  split_ifs with ht
  · exact deriv_putPrice_spot (r := r) (hpos p.1 p.2 ht) hK hσ (sub_pos.mpr ht)
  · rfl

/-- The call delta hedge bond holding along a continuous adapted positive spot process, with
a deterministic Borel bond price and zero extension at and after maturity, is predictable. -/
theorem isStronglyPredictable_hedgeBondHolding_callPrice
    (hS : StronglyAdapted ℱ S) (hc : ∀ ω, Continuous (fun t => S t ω))
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω) (hK : 0 < K) (hσ : σ ≠ 0)
    {β : ℝ≥0 → ℝ} (hβ : Measurable β) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then
      hedgeBondHolding (fun s => callPrice s r σ K (T - t)) (S t ω) (β t) else 0) := by
  have ht := ℱ.measurable_fst_predictable
  have htm := ht.coe_nnreal_real
  have hdPlus := measurable_dPlus_process (r := r) (σ := σ) (K := K) (T := T) hS hc
  have hd : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      dMinus (S p.1 p.2) r σ K (T - p.1)) := by
    simp only [dMinus_def]
    fun_prop
  have hΦ := (monotone_cdf (μ := gaussianReal 0 1)).measurable.comp hd
  have hh : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ) < T then
      -(K * exp (-r * (T - p.1)) * cdf (gaussianReal 0 1)
        (dMinus (S p.1 p.2) r σ K (T - p.1))) / β p.1 else 0) := by
    exact (((measurable_const.mul ((measurable_const.mul
      (measurable_const.sub htm)).exp)).mul hΦ).neg.div (hβ.comp ht)).ite
      (measurableSet_lt htm measurable_const)
      measurable_const
  rw [IsStronglyPredictable]
  convert hh.stronglyMeasurable using 1
  ext p
  simp only [Function.uncurry]
  split_ifs with ht
  · exact hedgeBondHolding_callPrice (r := r) (hpos p.1 p.2 ht) hK hσ (sub_pos.mpr ht) (β p.1)
  · rfl

/-- The put delta hedge bond holding along a continuous adapted positive spot process, with
a deterministic Borel bond price and zero extension at and after maturity, is predictable. -/
theorem isStronglyPredictable_hedgeBondHolding_putPrice
    (hS : StronglyAdapted ℱ S) (hc : ∀ ω, Continuous (fun t => S t ω))
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω) (hK : 0 < K) (hσ : σ ≠ 0)
    {β : ℝ≥0 → ℝ} (hβ : Measurable β) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then
      hedgeBondHolding (fun s => putPrice s r σ K (T - t)) (S t ω) (β t) else 0) := by
  have ht := ℱ.measurable_fst_predictable
  have htm := ht.coe_nnreal_real
  have hdPlus := measurable_dPlus_process (r := r) (σ := σ) (K := K) (T := T) hS hc
  have hd : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      dMinus (S p.1 p.2) r σ K (T - p.1)) := by
    simp only [dMinus_def]
    fun_prop
  have hΦ := (monotone_cdf (μ := gaussianReal 0 1)).measurable.comp hd.neg
  have hh : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ) < T then
      K * exp (-r * (T - p.1)) * cdf (gaussianReal 0 1)
        (-dMinus (S p.1 p.2) r σ K (T - p.1)) / β p.1 else 0) := by
    exact (((measurable_const.mul ((measurable_const.mul
      (measurable_const.sub htm)).exp)).mul hΦ).div (hβ.comp ht)).ite
      (measurableSet_lt htm measurable_const)
      measurable_const
  rw [IsStronglyPredictable]
  convert hh.stronglyMeasurable using 1
  ext p
  simp only [Function.uncurry]
  split_ifs with ht
  · exact hedgeBondHolding_putPrice (r := r) (hpos p.1 p.2 ht) hK hσ (sub_pos.mpr ht) (β p.1)
  · rfl

end MeasureTheory.StronglyAdapted
