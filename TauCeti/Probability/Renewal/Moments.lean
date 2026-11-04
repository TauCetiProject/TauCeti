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
`N t` decays geometrically. Past `M ≈ L t` arrivals, with `L` chosen so that `e · ρ(1) ^ L ≤ 1`,
the factor `exp t` is absorbed, which gives `𝔼[(N t) ^ p] ≤ C (t + 1) ^ p` with `C` independent
of `t`. Since the count is nondecreasing in time, these moments also bound the counts on every
bounded time interval. Finite moments supply the local integrability used for the renewal function
`m t = 𝔼[N t]`, and their polynomial growth gives the uniform integrability of `N t / t` behind
the elementary renewal theorem.

## Main results

* `TauCeti.Probability.measureReal_arrival_le_le_exp_mul_mgf_pow` — the Chernoff bound
  `P(arrival T n ≤ t) ≤ exp (s t) · mgf (T 0) P (-s) ^ n`.
* `TauCeti.Probability.exists_lintegral_renewalCount_pow_le` — `∫⁻ (N t) ^ p ≤ C (t + 1) ^ p`
  for a constant `C` independent of `t`.
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

/-- Off a null set the count is a natural number `m`. A count below `M` contributes at most
`M ^ p`, and a count `M + j` is the `j`-th term of a series of weighted tail probabilities. -/
private theorem lintegral_renewalCount_pow_le_add_tsum (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0) (p M : ℕ) :
    ∫⁻ ω, renewalCount T t ω ^ p ∂P ≤
      (M : ℝ≥0∞) ^ p + ∑' j : ℕ, ((M + j : ℕ) : ℝ≥0∞) ^ p * P {ω | arrival T (M + j) ω ≤ t} := by
  have := hindep.isProbabilityMeasure
  have hmeas : ∀ n, MeasurableSet {ω | arrival T n ω ≤ t} := fun n ↦
    measurableSet_le (measurable_arrival hT n) measurable_const
  have hle : ∀ᵐ ω ∂P, renewalCount T t ω ^ p ≤ (M : ℝ≥0∞) ^ p +
      ∑' j : ℕ, {ω | arrival T (M + j) ω ≤ t}.indicator (fun _ ↦ ((M + j : ℕ) : ℝ≥0∞) ^ p) ω := by
    filter_upwards [ae_renewalCount_lt_top hT hindep hid hzero] with ω hω
    obtain ⟨m, hm⟩ := exists_renewalCount_eq_natCast (hω t).ne
    rw [hm]
    rcases lt_or_ge m M with h | h
    · exact le_add_right (by gcongr)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      refine le_add_left (le_trans ?_ (_root_.le_tsum _ j))
      rw [indicator_of_mem (natCast_le_renewalCount_iff.1 hm.ge)]
  refine (lintegral_mono_ae hle).trans_eq ?_
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_tsum fun j ↦ (measurable_const.indicator (hmeas _)).aemeasurable]
  simp [lintegral_indicator_const (hmeas _)]

/-- If `exp 1 * ρ ^ L ≤ 1` for the Laplace transform `ρ` of the increment law at rate `1`, the
Chernoff bound at rate `1` absorbs the factor `exp t` after `L * ⌈t⌉₊` arrivals. -/
private theorem measureReal_arrival_le_le_pow_succ (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) {L : ℕ}
    (hL : exp 1 * mgf (fun ω ↦ (T 0 ω : ℝ)) P (-1) ^ L ≤ 1) (t : ℝ≥0) (j : ℕ) :
    P.real {ω | arrival T (L * ⌈t⌉₊ + 1 + j) ω ≤ t} ≤
      mgf (fun ω ↦ (T 0 ω : ℝ)) P (-1) ^ (j + 1) := by
  set ρ := mgf (fun ω ↦ (T 0 ω : ℝ)) P (-1)
  have hρ0 : 0 ≤ ρ := mgf_nonneg
  have hk : (t : ℝ) ≤ ⌈t⌉₊ := by exact_mod_cast Nat.le_ceil t
  refine (measureReal_arrival_le_le_exp_mul_mgf_pow hT hindep hid zero_le_one t _).trans ?_
  calc exp (1 * t) * ρ ^ (L * ⌈t⌉₊ + 1 + j) = exp t * ρ ^ (L * ⌈t⌉₊) * ρ ^ (j + 1) := by
        rw [add_assoc, add_comm 1 j, pow_add, one_mul, mul_assoc]
    _ ≤ exp ⌈t⌉₊ * ρ ^ (L * ⌈t⌉₊) * ρ ^ (j + 1) := by gcongr
    _ = (exp 1 * ρ ^ L) ^ ⌈t⌉₊ * ρ ^ (j + 1) := by rw [mul_pow, exp_one_pow, ← pow_mul]
    _ ≤ 1 ^ ⌈t⌉₊ * ρ ^ (j + 1) := by gcongr
    _ = ρ ^ (j + 1) := by simp

/-- **Polynomial growth of the moments of the renewal counts.** For independent, identically
distributed increments that are not almost surely zero, the `p`-th moment of the count grows at most
like the `p`-th power of time: there is a constant `C` with `∫⁻ (N t) ^ p ≤ C * (t + 1) ^ p` for
every `t`. No assumption is made on the mean of the increments. -/
theorem exists_lintegral_renewalCount_pow_le (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (p : ℕ) :
    ∃ C : ℝ≥0, ∀ t : ℝ≥0, ∫⁻ ω, renewalCount T t ω ^ p ∂P ≤ C * ((t + 1 : ℝ≥0) : ℝ≥0∞) ^ p := by
  have := hindep.isProbabilityMeasure
  -- The Laplace transform `ρ` of the increment law at rate `1` is strictly less than `1`.
  set ρ := mgf (fun ω ↦ (T 0 ω : ℝ)) P (-1)
  have hρ0 : 0 ≤ ρ := mgf_nonneg
  have hpos : P {ω | 0 < (T 0 ω : ℝ)} ≠ 0 := by
    have : {ω | 0 < (T 0 ω : ℝ)} = {ω | T 0 ω = 0}ᶜ := by
      ext ω
      simp [pos_iff_ne_zero]
    rw [this, Ne, prob_compl_eq_zero_iff (measurableSet_eq_fun (hT 0) measurable_const)]
    exact hzero.ne
  have hρ : ρ < 1 := mgf_lt_one_of_nonneg_of_neg (hT 0).coe_nnreal_real.aemeasurable
    (ae_of_all _ fun ω ↦ (T 0 ω).2) hpos (by norm_num)
  -- Choose `L` with `exp 1 * ρ ^ L ≤ 1`. After `M = L * ⌈t⌉₊ + 1` arrivals, the Chernoff factor
  -- `exp t` is absorbed and the tail decays like `ρ ^ (j + 1)`.
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (exp_pos (-1)) hρ
  have hL' : exp 1 * ρ ^ L ≤ 1 := by
    calc exp 1 * ρ ^ L ≤ exp 1 * exp (-1) := by gcongr
      _ = 1 := by rw [← exp_add]; simp
  have hsum : Summable fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) ^ p * ρ ^ (j + 1) :=
    (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ p * ρ ^ n) 1).2 <|
      summable_pow_mul_geometric_of_norm_lt_one p
      (by rwa [Real.norm_of_nonneg hρ0])
  set S := ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ p * ρ ^ (j + 1)
  have hS : 0 ≤ S := tsum_nonneg fun j ↦ by positivity
  have hC : 0 ≤ (1 + S) * (L + 1) ^ p := by positivity
  refine ⟨NNReal.mk _ hC, fun t ↦ ?_⟩
  set k := ⌈t⌉₊
  set M := L * k + 1
  -- Each tail term is at most `M ^ p * ((j + 1) ^ p * ρ ^ (j + 1))`.
  have hterm (j : ℕ) : ((M + j : ℕ) : ℝ≥0∞) ^ p * P {ω | arrival T (M + j) ω ≤ t} ≤
      ENNReal.ofReal ((M : ℝ) ^ p * (((j + 1 : ℕ) : ℝ) ^ p * ρ ^ (j + 1))) := by
    rw [← ofReal_measureReal (measure_ne_top _ _), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) p)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hchernoff := measureReal_arrival_le_le_pow_succ hT hindep hid hL' t j
    have hMj : ((M + j : ℕ) : ℝ) ^ p ≤ (M : ℝ) ^ p * ((j + 1 : ℕ) : ℝ) ^ p := by
      rw [← mul_pow]
      gcongr
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.le_add_left 1 (L * k)
      push_cast
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    rw [← mul_assoc]
    exact mul_le_mul hMj hchernoff measureReal_nonneg (by positivity)
  have hM : (M : ℝ) ≤ (L + 1) * ((t : ℝ) + 1) := by
    have hk : (k : ℝ) < t + 1 := Nat.ceil_lt_add_one t.2
    have ht : (0 : ℝ) ≤ t := t.2
    push_cast [M]
    nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  calc ∫⁻ ω, renewalCount T t ω ^ p ∂P
      ≤ (M : ℝ≥0∞) ^ p +
          ∑' j : ℕ, ((M + j : ℕ) : ℝ≥0∞) ^ p * P {ω | arrival T (M + j) ω ≤ t} :=
        lintegral_renewalCount_pow_le_add_tsum hT hindep hid hzero t p M
    _ ≤ ENNReal.ofReal ((M : ℝ) ^ p) +
          ∑' j : ℕ, ENNReal.ofReal ((M : ℝ) ^ p * (((j + 1 : ℕ) : ℝ) ^ p * ρ ^ (j + 1))) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _)]
        gcongr with j
        exact hterm j
    _ = ENNReal.ofReal ((1 + S) * (M : ℝ) ^ p) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity) (hsum.mul_left _),
          tsum_mul_left, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal ((1 + S) * (L + 1) ^ p * ((t : ℝ) + 1) ^ p) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc, ← mul_pow]
        gcongr
    _ = _ := by
        have ht : ENNReal.ofReal ((t : ℝ) + 1) = ((t + 1 : ℝ≥0) : ℝ≥0∞) := by
          rw [← NNReal.coe_one, ← NNReal.coe_add, ENNReal.ofReal_coe_nnreal]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ht,
          ENNReal.ofReal_eq_coe_nnreal hC]

/-- **Finite moments of the renewal counts.** For independent, identically distributed increments
that are not almost surely zero, every count `renewalCount T t` has a finite moment of every
order `p`. No assumption is made on the mean of the increments. -/
theorem lintegral_renewalCount_pow_lt_top (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (hzero : P {ω | T 0 ω = 0} < 1) (t : ℝ≥0)
    (p : ℕ) : ∫⁻ ω, renewalCount T t ω ^ p ∂P < ∞ := by
  obtain ⟨C, hC⟩ := exists_lintegral_renewalCount_pow_le hT hindep hid hzero p
  exact (hC t).trans_lt (by finiteness)

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
