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
when evaluated along a predictable positive spot process. The statements use the
existing spot derivative and `TauCeti.BlackScholes.hedgeBondHolding`, on the entire interval
before maturity, and extend each holding by zero at and after maturity. No terminal limit of
the delta is required, including at the strike. Continuous adapted spot processes satisfy the
predictability assumption by
`MeasureTheory.StronglyAdapted.isStronglyPredictable_of_continuous`.

The bond price may be any deterministic Borel function; continuous positive bonds are a
special case. These results supply predictable holdings for stochastic integration. They do
not assert integrability or self-financing.

The public theorems in `MeasureTheory.IsStronglyPredictable` are `deriv_callPrice_spot`,
`deriv_putPrice_spot`, `hedgeBondHolding_callPrice`, and `hedgeBondHolding_putPrice`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MeasureTheory.IsStronglyPredictable

open TauCeti.BlackScholes

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {S : ℝ≥0 → Ω → ℝ} {r σ K T : ℝ}

private theorem measurable_dPlus_process
    (hS : IsStronglyPredictable ℱ S) :
    Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      dPlus (S p.1 p.2) r σ K (T - p.1)) := by
  have hSm : Measurable[ℱ.predictable] (Function.uncurry S) :=
    hS.measurable
  have htm := (ℱ.measurable_fst_predictable).coe_nnreal_real
  simp only [dPlus_def]
  fun_prop

private theorem measurable_dMinus_process (hS : IsStronglyPredictable ℱ S) :
    Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω =>
      dMinus (S p.1 p.2) r σ K (T - p.1)) := by
  have hdPlus := measurable_dPlus_process (r := r) (σ := σ) (K := K) (T := T) hS
  have htm := (ℱ.measurable_fst_predictable).coe_nnreal_real
  simp only [dMinus_def]
  fun_prop

private theorem isStronglyPredictable_before_maturity
    {u : ℝ≥0 → Ω → ℝ} {f : ℝ≥0 × Ω → ℝ}
    (hf : Measurable[ℱ.predictable] f)
    (hu : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → u t ω = f (t, ω)) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then u t ω else 0) := by
  have hh := hf.isStronglyPredictable_ite_zero
    (measurableSet_lt measurable_coe_nnreal_real measurable_const (g := fun _ => T))
  convert hh using 1
  ext t ω
  split_ifs with ht
  · exact hu t ω ht
  · rfl

/-- The call delta along a predictable positive spot process, extended by zero at and
after maturity, is predictable. -/
theorem deriv_callPrice_spot
    (hS : IsStronglyPredictable ℱ S)
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω) (hK : 0 < K) (hσ : σ ≠ 0) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then
      deriv (fun s => callPrice s r σ K (T - t)) (S t ω) else 0) := by
  have hd := measurable_dPlus_process (r := r) (σ := σ) (K := K) (T := T) hS
  refine isStronglyPredictable_before_maturity
    ((monotone_cdf (μ := gaussianReal 0 1)).measurable.comp hd) ?_
  intro t ω ht
  exact TauCeti.BlackScholes.deriv_callPrice_spot
    (r := r) (hpos t ω ht) hK hσ (sub_pos.mpr ht)

/-- The put delta along a predictable positive spot process, extended by zero at and
after maturity, is predictable. -/
theorem deriv_putPrice_spot
    (hS : IsStronglyPredictable ℱ S)
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω) (hK : 0 < K) (hσ : σ ≠ 0) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then
      deriv (fun s => putPrice s r σ K (T - t)) (S t ω) else 0) := by
  have hd := measurable_dPlus_process (r := r) (σ := σ) (K := K) (T := T) hS
  refine isStronglyPredictable_before_maturity
    ((monotone_cdf (μ := gaussianReal 0 1)).measurable.comp hd.neg).neg ?_
  intro t ω ht
  exact TauCeti.BlackScholes.deriv_putPrice_spot
    (r := r) (hpos t ω ht) hK hσ (sub_pos.mpr ht)

/-- The call delta hedge bond holding along a predictable positive spot process, with
a deterministic Borel bond price and zero extension at and after maturity, is predictable. -/
theorem hedgeBondHolding_callPrice
    (hS : IsStronglyPredictable ℱ S)
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω) (hK : 0 < K) (hσ : σ ≠ 0)
    {β : ℝ≥0 → ℝ} (hβ : Measurable β) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then
      hedgeBondHolding (fun s => callPrice s r σ K (T - t)) (S t ω) (β t) else 0) := by
  have ht := ℱ.measurable_fst_predictable
  have htm := ht.coe_nnreal_real
  have hd := measurable_dMinus_process (r := r) (σ := σ) (K := K) (T := T) hS
  have hΦ := (monotone_cdf (μ := gaussianReal 0 1)).measurable.comp hd
  have hβm := hβ.comp ht
  refine isStronglyPredictable_before_maturity (f := fun p =>
    -(K * exp (-r * (T - p.1)) * cdf (gaussianReal 0 1)
      (dMinus (S p.1 p.2) r σ K (T - p.1))) / β p.1) (by fun_prop) ?_
  intro t ω ht
  exact TauCeti.BlackScholes.hedgeBondHolding_callPrice
    (r := r) (hpos t ω ht) hK hσ (sub_pos.mpr ht) (β t)

/-- The put delta hedge bond holding along a predictable positive spot process, with
a deterministic Borel bond price and zero extension at and after maturity, is predictable. -/
theorem hedgeBondHolding_putPrice
    (hS : IsStronglyPredictable ℱ S)
    (hpos : ∀ (t : ℝ≥0) ω, (t : ℝ) < T → 0 < S t ω) (hK : 0 < K) (hσ : σ ≠ 0)
    {β : ℝ≥0 → ℝ} (hβ : Measurable β) :
    IsStronglyPredictable ℱ (fun t ω => if (t : ℝ) < T then
      hedgeBondHolding (fun s => putPrice s r σ K (T - t)) (S t ω) (β t) else 0) := by
  have ht := ℱ.measurable_fst_predictable
  have htm := ht.coe_nnreal_real
  have hd := measurable_dMinus_process (r := r) (σ := σ) (K := K) (T := T) hS
  have hΦ := (monotone_cdf (μ := gaussianReal 0 1)).measurable.comp hd.neg
  have hβm := hβ.comp ht
  refine isStronglyPredictable_before_maturity (f := fun p =>
    K * exp (-r * (T - p.1)) * cdf (gaussianReal 0 1)
      (-dMinus (S p.1 p.2) r σ K (T - p.1)) / β p.1) (by fun_prop) ?_
  intro t ω ht
  exact TauCeti.BlackScholes.hedgeBondHolding_putPrice
    (r := r) (hpos t ω ht) hK hσ (sub_pos.mpr ht) (β t)

end MeasureTheory.IsStronglyPredictable
