/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Renewal.Measure
public import TauCeti.Probability.Distributions.Binomial.ConvolutionPower
public import TauCeti.Probability.Distributions.Binomial.Tail
public import TauCeti.Probability.Distributions.NegativeBinomial.Cdf
public import TauCeti.Probability.Distributions.NegativeBinomial.Transforms
import TauCeti.Probability.Distributions.Bernoulli.Basic
import TauCeti.Probability.Independence.InfinitePi

/-!
# Renewal processes with two-point increments

For increments equal to `a > 0` with probability `q > 0` and zero otherwise, the count at
time `t` is a shifted negative-binomial variable. Write `k = ⌊t / a⌋₊`. The count includes the
zero increments before the `(k + 1)`-st positive increment, so its law is that of
`k + NegativeBinomial(k + 1, q)`. In particular, arrivals at time zero are counted.

The renewal measure gives `[0,t]` mass `(k + 1) / q`, and the renewal function is
`(k + 1) / q - 1`. These formulas include deterministic increments at `q = 1`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {T : ℕ → Ω → ℝ≥0} {a : ℝ≥0} {q : unitInterval}

/-- The arrival times for two-point increments have scaled binomial laws. -/
theorem hasLaw_arrival_binomial (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (T n) (bernoulliMeasure a 0 q) P) (n : ℕ) :
    HasLaw (arrival T n) ((binomial n q).map (fun j : ℕ ↦ (j : ℝ≥0) * a)) P := by
  have h := hasLaw_arrival hindep (fun n ↦ (hlaw n).identDistrib (hlaw 0)) n
  rw [(hlaw 0).map_eq, bernoulliMeasure_convolutionPower_multiples] at h
  convert h using 1
  congr 1
  funext j
  simp

/-- Two-point increments with a positive chance of a strictly positive increment do not explode.
Zero increments and success probability one are both allowed. -/
theorem ae_tendsto_arrival_atTop_of_bernoulliMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hlaw : ∀ n, HasLaw (T n) (bernoulliMeasure a 0 q) P)
    (ha : 0 < a) (hq : 0 < (q : ℝ)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop := by
  have := hindep.isProbabilityMeasure
  refine ae_tendsto_arrival_atTop hT hindep (fun n ↦ (hlaw n).identDistrib (hlaw 0)) ?_
  rw [(hlaw 0).measure_eq (p := fun x ↦ x = 0) (measurableSet_singleton 0)]
  exact bernoulliMeasure_singleton_zero_lt_one ha.ne' hq

/-- The cdf of a two-point renewal count is the upper binomial tail at `⌊t/a⌋₊`.
This includes both endpoints of the time interval and all zero-time arrivals. -/
theorem measure_renewalCountNat_le_of_bernoulliMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hlaw : ∀ n, HasLaw (T n) (bernoulliMeasure a 0 q) P)
    (ha : 0 < a) (hq : 0 < (q : ℝ)) (t : ℝ≥0) (n : ℕ) :
    P {ω | renewalCountNat T t ω ≤ n} = binomial (n + 1) q (Ioi ⌊t / a⌋₊) := by
  have := hindep.isProbabilityMeasure
  have hae : {ω | renewalCountNat T t ω ≤ n} =ᵐ[P]
      {ω | t < arrival T (n + 1) ω} := by
    filter_upwards [ae_tendsto_arrival_atTop_of_bernoulliMeasure hT hindep hlaw ha hq]
      with ω hω
    apply propext
    rw [← not_le, ← le_renewalCountNat_iff hω]
    omega
  rw [measure_congr hae,
    (hasLaw_arrival_binomial hindep hlaw (n + 1)).measure_eq measurableSet_Ioi,
    Ioi_def,
    Measure.map_apply Measurable.of_discrete (measurableSet_Ioi (a := t))]
  congr 1
  ext j
  simp only [mem_preimage, mem_Ioi]
  rw [Nat.floor_lt (by positivity), div_lt_iff₀ ha]

/-- The renewal count for increments in `{0,a}` is a shifted negative-binomial variable.
With `k = ⌊t/a⌋₊`, it counts `k` positive increments and the failures preceding the next one. -/
theorem hasLaw_renewalCountNat_negativeBinomialMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hlaw : ∀ n, HasLaw (T n) (bernoulliMeasure a 0 q) P)
    (ha : 0 < a) (hq : 0 < (q : ℝ)) (t : ℝ≥0) :
    HasLaw (renewalCountNat T t)
      ((negativeBinomialMeasure (⌊t / a⌋₊ + 1) q).map (fun j ↦ ⌊t / a⌋₊ + j)) P := by
  have := hindep.isProbabilityMeasure
  let k := ⌊t / a⌋₊
  have hk : (0 : ℝ) < k + 1 := by positivity
  let _ := isProbabilityMeasure_negativeBinomialMeasure hk.le hq q.2.2
  refine ⟨(measurable_renewalCountNat hT t).aemeasurable,
    Measure.ext_of_Iic _ _ fun n ↦ ?_⟩
  rw [Measure.map_apply (measurable_renewalCountNat hT t) measurableSet_Iic,
    Measure.map_apply Measurable.of_discrete measurableSet_Iic]
  simp only [← Iic_def, preimage_ofPred_eq]
  rw [measure_renewalCountNat_le_of_bernoulliMeasure hT hindep hlaw ha hq]
  by_cases hkn : k ≤ n
  · have hpre : {j : ℕ | k + j ≤ n} = Iic (n - k) := by
      ext j
      simp only [mem_ofPred_eq, mem_Iic]
      omega
    rw [hpre]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [← measureReal_def, ← measureReal_def, negativeBinomialMeasure_real_Iic hk hq q.2.2]
    have htail := binomial_tail_eq_regularizedIncompleteBeta
      (n := n + 1) (m := k + 1) (by omega) q
    have hset : Ioi k = {j : ℕ | k + 1 ≤ j} := by
      ext j
      simp only [mem_Ioi, mem_ofPred_eq]
      omega
    rw [hset, htail]
    congr 1 <;> push_cast [Nat.cast_sub hkn] <;> ring
  · have hpre : {j : ℕ | k + j ≤ n} = ∅ := by
      ext j
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      omega
    rw [hpre, measure_empty]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_le_of_hasLaw_binomial
      (HasLaw.id (μ := binomial (n + 1) q))] with j hj
    simp only [mem_Ioi, not_lt]
    exact hj.trans (by omega)

/-- Arrivals at zero have a geometric law: they are the zero increments preceding the first
positive increment. The artificial arrival `arrival T 0 = 0` is excluded. -/
theorem hasLaw_renewalCountNat_zero_geometricMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hlaw : ∀ n, HasLaw (T n) (bernoulliMeasure a 0 q) P)
    (ha : 0 < a) (hq : 0 < (q : ℝ)) :
    HasLaw (renewalCountNat T 0) (geometricMeasure q) P := by
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  simpa [geometricMeasure_eq_negativeBinomialMeasure_one q hq0] using
    hasLaw_renewalCountNat_negativeBinomialMeasure hT hindep hlaw ha hq 0

/-- The expected number of two-point renewal arrivals through time `t` is
`(⌊t/a⌋₊ + 1) / q - 1`. In particular the mean at time zero is `(1-q)/q`. -/
theorem integral_renewalCountNat_of_bernoulliMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hlaw : ∀ n, HasLaw (T n) (bernoulliMeasure a 0 q) P)
    (ha : 0 < a) (hq : 0 < (q : ℝ)) (t : ℝ≥0) :
    ∫ ω, (renewalCountNat T t ω : ℝ) ∂P = (⌊t / a⌋₊ + 1) / (q : ℝ) - 1 := by
  have := hindep.isProbabilityMeasure
  let k := ⌊t / a⌋₊
  let ν := negativeBinomialMeasure (k + 1) q
  have hk : (0 : ℝ) ≤ k + 1 := by positivity
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_negativeBinomialMeasure hk hq q.2.2
  have hcast : HasLaw (Nat.cast : ℕ → ℝ) (ν.map (Nat.cast : ℕ → ℝ)) ν :=
    ⟨Measurable.of_discrete.aemeasurable, rfl⟩
  have hi : Integrable (fun j : ℕ ↦ (j : ℝ)) ν :=
    hcast.integrable ((memLp_id_map_cast_negativeBinomialMeasure hk hq q.2.2 1).integrable
      (by simp))
  have hshift : HasLaw (fun j : ℕ ↦ k + j) (ν.map (fun j ↦ k + j)) ν :=
    ⟨Measurable.of_discrete.aemeasurable, rfl⟩
  rw [← Function.comp_def (fun j : ℕ ↦ (j : ℝ)),
    (hasLaw_renewalCountNat_negativeBinomialMeasure hT hindep hlaw ha hq t).integral_comp
      .of_discrete, ← hshift.integral_comp (f := fun j : ℕ ↦ (j : ℝ)) .of_discrete]
  simp only [Function.comp_apply, Nat.cast_add]
  rw [integral_add (integrable_const _) hi, integral_const, probReal_univ, one_smul,
    hcast.integral_eq, integral_id_map_cast_negativeBinomialMeasure hk hq q.2.2]
  field_simp; ring

/-- The renewal function of a two-point law, as a real number, is `(⌊t/a⌋₊ + 1) / q - 1`.
It counts genuine zero increments but excludes the artificial point mass `δ₀`. -/
theorem toReal_renewalFunction_bernoulliMeasure (ha : 0 < a) (hq : 0 < (q : ℝ)) (t : ℝ≥0) :
    ((bernoulliMeasure a 0 q).renewalFunction t).toReal =
      (⌊t / a⌋₊ + 1) / (q : ℝ) - 1 := by
  let μ := bernoulliMeasure a 0 q
  let P := Measure.infinitePi fun _ : ℕ ↦ μ
  have hT : ∀ n, Measurable fun ω : ℕ → ℝ≥0 ↦ ω n := measurable_pi_apply
  have hindep : iIndepFun _ P := iIndepFun_eval_infinitePi _
  have hlaw (n : ℕ) : HasLaw (fun ω : ℕ → ℝ≥0 ↦ ω n) μ P :=
    ⟨(hT n).aemeasurable, Measure.infinitePi_map_eval _ n⟩
  have hzero : P {ω | ω 0 = 0} < 1 := by
    rw [(hlaw 0).measure_eq (p := fun x ↦ x = 0) (measurableSet_singleton 0)]
    exact bernoulliMeasure_singleton_zero_lt_one ha.ne' hq
  have hmean := integral_renewalCountNat hT hindep
    (fun n ↦ (hlaw n).identDistrib (hlaw 0)) hzero t
  rw [(hlaw 0).map_eq] at hmean
  exact hmean.symm.trans
    (integral_renewalCountNat_of_bernoulliMeasure hT hindep hlaw ha hq t)

/-- The cumulative renewal mass of a two-point law through `t` is `(⌊t/a⌋₊ + 1) / q`,
including the artificial arrival and all genuine arrivals at zero. -/
theorem renewalMeasure_bernoulliMeasure_real_Iic (ha : 0 < a) (hq : 0 < (q : ℝ)) (t : ℝ≥0) :
    (bernoulliMeasure a 0 q).renewalMeasure.real (Iic t) =
      (⌊t / a⌋₊ + 1) / (q : ℝ) := by
  have hzero := bernoulliMeasure_singleton_zero_lt_one ha.ne' hq
  rw [measureReal_def, Measure.renewalMeasure_Iic,
    ENNReal.toReal_add ENNReal.one_ne_top
      (Measure.renewalFunction_lt_top _ hzero t).ne, ENNReal.toReal_one,
    toReal_renewalFunction_bernoulliMeasure ha hq]
  ring

end TauCeti.Probability
