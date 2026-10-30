/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Probability.Moments.Basic
public import TauCeti.Probability.Renewal.Basic

/-!
# Finite moments of the renewal counts

Let `T 0, T 1, …` be independent, identically distributed nonnegative increments that are not
almost surely zero, with arrival times `arrival T n` and counts `renewalCount T t` as in
`TauCeti.Probability.Renewal.Basic`. This file shows that every count has finite moments of every
order, without any assumption on the mean of the increments: the mean may be infinite.

The argument is a Chernoff bound for the lower tail of the arrival times. Writing
`ρ(s) = 𝔼[exp (-s T 0)]` for the Laplace transform of the increment law at rate `s ≥ 0`, Markov's
inequality and independence give

```text
P(n ≤ N t) = P(arrival T n ≤ t) ≤ exp (s t) · ρ(s) ^ n,
```

and `ρ(s) < 1` for `s > 0` because the increments are not almost surely zero. So the tail of
`N t` decays geometrically and `𝔼[(N t) ^ p] ≤ ∑ n, n ^ p · P(arrival T n ≤ t)` is finite. Since
the count is nondecreasing in time, these moments also bound the counts on every bounded time
interval. Finite moments supply the local integrability used for the renewal function
`m t = 𝔼[N t]` and for the integrability arguments behind the renewal limit theorems.

## Main results

* `TauCeti.Probability.measureReal_arrival_le_le_exp_mul_mgf_pow` — the Chernoff bound
  `P(arrival T n ≤ t) ≤ exp (s t) · mgf (T 0) P (-s) ^ n`.
* `TauCeti.Probability.lintegral_renewalCount_pow_lt_top` — `∫⁻ (N t) ^ p < ∞` for every `p : ℕ`.
* `TauCeti.Probability.memLp_toReal_renewalCount` — the real-valued count lies in `Lᵖ` for every
  finite `p`.
* `TauCeti.Probability.integrable_toReal_renewalCount` — the real-valued count is integrable.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- **Chernoff bound for the arrival times.** For independent, identically distributed increments
and every rate `s ≥ 0`, the probability that the `n`-th arrival is at most `t` is at most
`exp (s t)` times the `n`-th power of the Laplace transform `mgf (T 0) P (-s)` of the increment
law. By `natCast_le_renewalCount_iff` this is also a bound on `P(n ≤ renewalCount T t)`. -/
theorem measureReal_arrival_le_le_exp_mul_mgf_pow (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) {s : ℝ} (hs : 0 ≤ s)
    (t : ℝ≥0) (n : ℕ) :
    P.real {ω | arrival T n ω ≤ t} ≤ exp (s * t) * mgf (fun ω ↦ (T 0 ω : ℝ)) P (-s) ^ n := by
  have := hindep.isProbabilityMeasure
  set X : ℕ → Ω → ℝ := fun i ω ↦ T i ω
  have hXm : ∀ i, Measurable (X i) := fun i ↦ (hT i).coe_nnreal_real
  have hXi : iIndepFun X P := hindep.comp (fun _ x ↦ (x : ℝ)) fun _ ↦ measurable_coe_nnreal_real
  have hsum : ∀ ω, (∑ i ∈ Finset.range n, X i) ω = arrival T n ω := fun ω ↦ by
    simp [X, arrival_def]
  have hint : Integrable (fun ω ↦ exp (-s * (∑ i ∈ Finset.range n, X i) ω)) P := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff, hsum]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hs) (arrival T n ω).2
  have hset : {ω | arrival T n ω ≤ t} = {ω | (∑ i ∈ Finset.range n, X i) ω ≤ t} := by
    ext ω
    simp [hsum]
  rw [hset]
  refine (measure_le_le_exp_mul_mgf (t : ℝ) (neg_nonpos.2 hs) hint).trans_eq ?_
  rw [neg_neg, hXi.mgf_sum hXm, Finset.prod_eq_pow_card fun i _ ↦
    mgf_congr_of_identDistrib (X i) (fun ω ↦ (T 0 ω : ℝ))
      ((hid i).comp measurable_coe_nnreal_real) (-s), Finset.card_range]

/-- **Finite moments of the renewal counts.** For independent, identically distributed increments
that are not almost surely zero, every count `renewalCount T t` has a finite moment of every
order `p`. No assumption is made on the mean of the increments. -/
theorem lintegral_renewalCount_pow_lt_top (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0)
    (p : ℕ) : ∫⁻ ω, renewalCount T t ω ^ p ∂P < ∞ := by
  have := hindep.isProbabilityMeasure
  -- The Laplace transform `ρ` of the increment law at rate `1` is strictly less than `1`.
  set ρ := mgf (fun ω ↦ (T 0 ω : ℝ)) P (-1)
  have hpos : P {ω | 0 < (T 0 ω : ℝ)} ≠ 0 := by
    have : {ω | 0 < (T 0 ω : ℝ)} = {ω | T 0 ω = 0}ᶜ := by
      ext ω
      simp [pos_iff_ne_zero]
    rw [this, Ne, prob_compl_eq_zero_iff (measurableSet_eq_fun (hT 0) measurable_const)]
    exact hzero.ne
  have hρ : ρ < 1 := mgf_lt_one_of_nonneg_of_neg (hT 0).coe_nnreal_real.aemeasurable
    (ae_of_all _ fun ω ↦ (T 0 ω).2) hpos (by norm_num)
  have hsum : Summable fun n : ℕ ↦ (n : ℝ) ^ p * (exp t * ρ ^ n) :=
    ((summable_pow_mul_geometric_of_norm_lt_one p
      (by rwa [Real.norm_of_nonneg mgf_nonneg])).mul_left (exp t)).congr fun n ↦ by ring
  -- Off a null set the count is a natural number `m`, and then `m ^ p` is the `m`-th term of
  -- the series of weighted tail probabilities.
  have hle : ∀ᵐ ω ∂P, renewalCount T t ω ^ p ≤
      ∑' n : ℕ, {ω | arrival T n ω ≤ t}.indicator (fun _ ↦ (n : ℝ≥0∞) ^ p) ω := by
    filter_upwards [ae_renewalCount_lt_top hT hindep hid hzero] with ω hω
    obtain ⟨m, hm⟩ := exists_renewalCount_eq_natCast (hω t).ne
    refine le_trans ?_ (ENNReal.le_tsum m)
    rw [hm, indicator_of_mem (natCast_le_renewalCount_iff.1 hm.ge)]
  calc ∫⁻ ω, renewalCount T t ω ^ p ∂P
      ≤ ∫⁻ ω, ∑' n : ℕ, {ω | arrival T n ω ≤ t}.indicator (fun _ ↦ (n : ℝ≥0∞) ^ p) ω ∂P :=
        lintegral_mono_ae hle
    _ = ∑' n : ℕ, (n : ℝ≥0∞) ^ p * P {ω | arrival T n ω ≤ t} := by
        have hmeas : ∀ n, MeasurableSet {ω | arrival T n ω ≤ t} := fun n ↦
          measurableSet_le (measurable_arrival hT n) measurable_const
        rw [lintegral_tsum fun n ↦ (measurable_const.indicator (hmeas n)).aemeasurable]
        exact tsum_congr fun n ↦ lintegral_indicator_const (hmeas n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ p * (exp t * ρ ^ n)) := by
        refine ENNReal.tsum_le_tsum fun n ↦ ?_
        rw [← ofReal_measureReal (measure_ne_top _ _),
          ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg n) p), ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_pow (Nat.cast_nonneg n)]
        gcongr
        simpa using measureReal_arrival_le_le_exp_mul_mgf_pow hT hindep hid zero_le_one t n
    _ < ∞ := by
        have hρ0 : 0 ≤ ρ := mgf_nonneg
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum]
        exact ENNReal.ofReal_lt_top

/-- For independent, identically distributed increments that are not almost surely zero, the
real-valued count `(renewalCount T t).toReal` lies in `Lᵖ` for every finite exponent `p`. It
agrees almost surely with the count, which is almost surely finite. -/
theorem memLp_toReal_renewalCount (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0)
    {p : ℝ≥0∞} (hp : p ≠ ∞) : MemLp (fun ω ↦ (renewalCount T t ω).toReal) p P := by
  have := hindep.isProbabilityMeasure
  -- Prove membership for the integer exponent `k = ⌈p⌉₊ + 1 ≥ p` and lower the exponent.
  set k : ℕ := ⌈p.toReal⌉₊ + 1
  have hk : MemLp (fun ω ↦ (renewalCount T t ω).toReal) k P := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp [k]) (by simp)
      (measurable_renewalCount hT t).ennreal_toReal.aestronglyMeasurable]
    refine lt_of_le_of_lt (lintegral_mono fun ω ↦ ?_)
      (lintegral_renewalCount_pow_lt_top hT hindep hid hzero t k)
    rw [ENNReal.toReal_natCast, ENNReal.rpow_natCast, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
    gcongr
    exact ENNReal.ofReal_toReal_le
  refine hk.mono_exponent ?_
  rw [← ENNReal.ofReal_toReal hp, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal ((Nat.le_ceil _).trans (by simp [k]))

/-- For independent, identically distributed increments that are not almost surely zero, the
real-valued count `(renewalCount T t).toReal` is integrable. -/
theorem integrable_toReal_renewalCount (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0) :
    Integrable (fun ω ↦ (renewalCount T t ω).toReal) P :=
  memLp_one_iff_integrable.1 (memLp_toReal_renewalCount hT hindep hid hzero t ENNReal.one_ne_top)

end TauCeti.Probability
