/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.Analysis.SpecialFunctions.Integrals.MellinWeight

/-!
# Weighted prime sums and their Mellin smoothing

For weights `a : ℕ → E` in a real Banach space `E`, the weighted prime sum is

`weightedPrimeSum a x = Σ_{p ≤ x} (log p / p) • a p`,

the finite sum over Mathlib's `Nat.primesLE ⌊x⌋₊`. Real, signed and complex weights are all
instances of this one definition.

For weights bounded by `1` on primes and `η > 0`, the Mellin smoothing of this step function
recovers the prime series with the exponent shifted by `η`:

`Σ_p (log p / p^(1+η)) • a p = η ∫_{t > 1} t^(-1-η) • weightedPrimeSum a t dt`.

The proof is partial summation at a finite cutoff `N`, followed by the limit `N → ∞`: the
boundary term `N^(-η) • weightedPrimeSum a N` tends to zero and the truncated integrals converge,
both by the elementary bound `‖weightedPrimeSum a t‖ ≤ (1 + log t)²`.

## Main results

* `TauCeti.weightedPrimeSum`: the weighted prime sum `Σ_{p ≤ x} (log p / p) • a p`;
* `TauCeti.weightedPrimeSum_eq_zero_of_lt_two`: it vanishes for `x < 2`;
* `TauCeti.weightedPrimeSum_congr`: it depends on `a` only through its values at primes;
* `TauCeti.weightedPrimeSum_add`, `TauCeti.weightedPrimeSum_smul`, `TauCeti.weightedPrimeSum_neg`,
  `TauCeti.weightedPrimeSum_sub`: linearity in the weights;
* `TauCeti.norm_weightedPrimeSum_le`: `‖weightedPrimeSum a t‖ ≤ (1 + log t)²` when `‖a p‖ ≤ 1`;
* `TauCeti.smul_intervalIntegral_rpow_smul_weightedPrimeSum`: the finite-cutoff partial summation
  formula;
* `TauCeti.integrableOn_rpow_smul_weightedPrimeSum`: Bochner integrability of `t^(-1-η) • A(t)`
  on `(1, ∞)`;
* `TauCeti.summable_weightedPrimeSeries`, `TauCeti.hasSum_weightedPrimeSeries`,
  `TauCeti.tsum_weightedPrimeSeries`: summability of `Σ_p (log p / p^(1+η)) • a p` over
  `Nat.Primes` and the Mellin identity.
-/

public section

open Filter MeasureTheory Real Set
open scoped Interval Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weighted prime sum `Σ_{p ≤ x} (log p / p) • a p`, as a finite sum over the primes in
`Nat.primesLE ⌊x⌋₊`. -/
noncomputable def weightedPrimeSum (a : ℕ → E) (x : ℝ) : E :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, (log p / p) • a p

theorem weightedPrimeSum_def (a : ℕ → E) (x : ℝ) :
    weightedPrimeSum a x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (log p / p) • a p := (rfl)

theorem weightedPrimeSum_natCast (a : ℕ → E) (n : ℕ) :
    weightedPrimeSum a n = ∑ p ∈ Nat.primesLE n, (log p / p) • a p := by
  rw [weightedPrimeSum_def, Nat.floor_natCast]

/-- The weighted prime sum only sees the integer part of the cutoff. -/
theorem weightedPrimeSum_natFloor (a : ℕ → E) (x : ℝ) :
    weightedPrimeSum a ⌊x⌋₊ = weightedPrimeSum a x := by
  rw [weightedPrimeSum_natCast, weightedPrimeSum_def]

/-- The weighted prime sum is constant on `[n, n + 1)`. -/
theorem weightedPrimeSum_of_mem_Ico (a : ℕ → E) {n : ℕ} {x : ℝ} (hx : x ∈ Ico (n : ℝ) (n + 1)) :
    weightedPrimeSum a x = weightedPrimeSum a n := by
  rw [← weightedPrimeSum_natFloor, Nat.floor_eq_on_Ico n x hx]

/-- The weighted prime sum vanishes below the first prime. -/
theorem weightedPrimeSum_eq_zero_of_lt_two (a : ℕ → E) {x : ℝ} (hx : x < 2) :
    weightedPrimeSum a x = 0 := by
  have h : ⌊x⌋₊ < 2 := (Nat.floor_lt' two_ne_zero).2 (by exact_mod_cast hx)
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have := Nat.two_le_of_mem_primesLE hp
  have := Nat.le_of_mem_primesLE hp
  omega

/-- The recursion for the weighted prime sum at successive integers. -/
theorem weightedPrimeSum_natCast_succ (a : ℕ → E) (n : ℕ) :
    weightedPrimeSum a (n + 1 : ℕ) = weightedPrimeSum a n +
      if (n + 1).Prime then (log (n + 1 : ℕ) / (n + 1 : ℕ)) • a (n + 1) else 0 := by
  rw [weightedPrimeSum_natCast, weightedPrimeSum_natCast, Nat.primesLE_succ]
  split_ifs
  · rw [Finset.sum_insert (Nat.notMem_primesLE n), add_comm]
  · rw [add_zero]

/-- The weighted prime sum depends on the weights only through their values at primes. -/
theorem weightedPrimeSum_congr {a b : ℕ → E} (h : ∀ p, p.Prime → a p = b p) :
    weightedPrimeSum a = weightedPrimeSum b := by
  ext x
  exact Finset.sum_congr rfl fun p hp ↦ by rw [h p (Nat.prime_of_mem_primesLE hp)]

@[simp] theorem weightedPrimeSum_zero : weightedPrimeSum (0 : ℕ → E) = 0 := by
  ext x
  simp [weightedPrimeSum_def]

theorem weightedPrimeSum_add (a b : ℕ → E) :
    weightedPrimeSum (a + b) = weightedPrimeSum a + weightedPrimeSum b := by
  ext x
  simp [weightedPrimeSum_def, Finset.sum_add_distrib]

theorem weightedPrimeSum_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (c : 𝕜) (a : ℕ → E) :
    weightedPrimeSum (c • a) = c • weightedPrimeSum a := by
  ext x
  simp [weightedPrimeSum_def, Finset.smul_sum, smul_comm _ c]

@[simp] theorem weightedPrimeSum_neg (a : ℕ → E) :
    weightedPrimeSum (-a) = -weightedPrimeSum a := by
  simpa using weightedPrimeSum_smul (-1 : ℝ) a

theorem weightedPrimeSum_sub (a b : ℕ → E) :
    weightedPrimeSum (a - b) = weightedPrimeSum a - weightedPrimeSum b := by
  rw [sub_eq_add_neg, weightedPrimeSum_add, weightedPrimeSum_neg, sub_eq_add_neg]

/-- The elementary bound `‖Σ_{p ≤ t} (log p / p) • a p‖ ≤ (1 + log t)²` for weights bounded by `1`
on primes, from `log p ≤ log t` and the harmonic bound `Σ_{k ≤ t} 1/k ≤ 1 + log t`. -/
theorem norm_weightedPrimeSum_le {a : ℕ → E} (ha : ∀ p, p.Prime → ‖a p‖ ≤ 1) (t : ℝ) :
    ‖weightedPrimeSum a t‖ ≤ (1 + log t) ^ 2 := by
  rcases lt_or_ge t 2 with ht | ht
  · rw [weightedPrimeSum_eq_zero_of_lt_two a ht, norm_zero]
    positivity
  set n := ⌊t⌋₊
  have hn1 : 1 ≤ n := Nat.le_floor (by norm_num; linarith)
  have hnt : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn : 0 ≤ log n := log_nonneg (by exact_mod_cast hn1)
  have hlog : log n ≤ log t := log_le_log hn0 hnt
  calc ‖weightedPrimeSum a t‖ ≤ ∑ p ∈ Nat.primesLE n, log p / p := by
        rw [weightedPrimeSum_def]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.one_lt_of_mem_primesLE hp).le
        have hlp : 0 ≤ log p / p := div_nonneg (log_nonneg hp1) (by linarith)
        rw [norm_smul, norm_of_nonneg hlp]
        exact mul_le_of_le_one_right hlp (ha p (Nat.prime_of_mem_primesLE hp))
    _ ≤ ∑ k ∈ Finset.Icc 1 n, log n * (k : ℝ)⁻¹ := by
        calc ∑ p ∈ Nat.primesLE n, log p / p ≤ ∑ p ∈ Nat.primesLE n, log n * (p : ℝ)⁻¹ := by
              refine Finset.sum_le_sum fun p hp ↦ ?_
              have hp0 : (0 : ℝ) < p := by
                exact_mod_cast (Nat.one_lt_of_mem_primesLE hp).trans' one_pos
              rw [div_eq_mul_inv]
              refine mul_le_mul_of_nonneg_right (log_le_log hp0 ?_) (inv_nonneg.2 hp0.le)
              exact_mod_cast Nat.le_of_mem_primesLE hp
          _ ≤ ∑ k ∈ Finset.Icc 1 n, log n * (k : ℝ)⁻¹ := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ ↦ by positivity
              rw [Nat.primesLE_eq_filter_Icc_one]
              exact Finset.filter_subset _ _
    _ = log n * harmonic n := by
        rw [← Finset.mul_sum]
        simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ log n * (1 + log n) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) hlogn
    _ ≤ (1 + log t) ^ 2 := by nlinarith

/-! ### Partial summation at a finite cutoff -/

/-- On `[n, n + 1]` the weighted integrand agrees almost everywhere with `t^(-1-η) • A(n)`. -/
private theorem ae_rpow_smul_weightedPrimeSum_eq (a : ℕ → E) (η : ℝ) (n : ℕ) :
    ∀ᵐ t ∂volume, t ∈ Ι (n : ℝ) (n + 1) →
      t ^ (-1 - η) • weightedPrimeSum a t = t ^ (-1 - η) • weightedPrimeSum a n := by
  filter_upwards [Measure.ae_ne volume ((n : ℝ) + 1)] with t hne ht
  rw [uIoc_of_le (by linarith)] at ht
  rw [weightedPrimeSum_of_mem_Ico a ⟨ht.1.le, lt_of_le_of_ne ht.2 hne⟩]

/-- The weighted integrand is interval integrable on each step `[n, n + 1]` with `n ≥ 1`. -/
theorem intervalIntegrable_rpow_smul_weightedPrimeSum_succ (a : ℕ → E) (η : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    IntervalIntegrable (fun t ↦ t ^ (-1 - η) • weightedPrimeSum a t) volume n (n + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine (ContinuousOn.intervalIntegrable ?_).congr_ae (EventuallyEq.symm
    ((ae_restrict_iff' measurableSet_uIoc).2 (ae_rpow_smul_weightedPrimeSum_eq a η n)))
  refine ContinuousOn.smul (fun t ht ↦ ?_) continuousOn_const
  refine (continuousAt_rpow_const _ _ (Or.inl ?_)).continuousWithinAt
  rw [uIcc_of_le (by linarith)] at ht
  exact (hn0.trans_le ht.1).ne'

/-- The weighted integrand is interval integrable on `[1, n]`. -/
theorem intervalIntegrable_rpow_smul_weightedPrimeSum (a : ℕ → E) (η : ℝ) (n : ℕ) :
    IntervalIntegrable (fun t ↦ t ^ (-1 - η) • weightedPrimeSum a t) volume 1 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (intervalIntegrable_const (c := (0 : E))).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun t ht ↦ ?_))
    rw [Nat.cast_zero, uIoc_of_ge zero_le_one] at ht
    simp only [weightedPrimeSum_eq_zero_of_lt_two a (by linarith [ht.2] : t < 2), smul_zero]
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    push_cast
    exact ih.trans (intervalIntegrable_rpow_smul_weightedPrimeSum_succ a η hn)

/-- The integral over one step `[n, n + 1]`. -/
private theorem integral_rpow_smul_weightedPrimeSum_succ [CompleteSpace E] (a : ℕ → E)
    {η : ℝ} (hη : η ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in (n : ℝ)..(n + 1), t ^ (-1 - η) • weightedPrimeSum a t =
      (((n : ℝ) ^ (-η) - ((n : ℝ) + 1) ^ (-η)) / η) • weightedPrimeSum a n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [intervalIntegral.integral_congr_ae (ae_rpow_smul_weightedPrimeSum_eq a η n),
    intervalIntegral.integral_smul_const, integral_rpow (Or.inr ⟨?_, ?_⟩)]
  · congr 1
    rw [show -1 - η + 1 = -η by ring, div_neg, ← neg_div, neg_sub]
  · intro h
    exact hη (by linarith)
  · rw [uIcc_of_le (by linarith)]
    exact fun h ↦ hn0.not_ge h.1

/-- **Partial summation at a finite cutoff**: for `n ≥ 1`,
`η ∫_1^n t^(-1-η) • A(t) dt = Σ_{p ≤ n} (log p / p^(1+η)) • a p - n^(-η) • A(n)`. -/
theorem smul_intervalIntegral_rpow_smul_weightedPrimeSum [CompleteSpace E] (a : ℕ → E)
    {η : ℝ} (hη : η ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    η • ∫ t in (1 : ℝ)..n, t ^ (-1 - η) • weightedPrimeSum a t =
      ∑ p ∈ Nat.primesLE n, (log p / (p : ℝ) ^ (1 + η)) • a p -
        (n : ℝ) ^ (-η) • weightedPrimeSum a n := by
  induction n, hn using Nat.le_induction with
  | base => simp [Nat.primesLE_one, weightedPrimeSum_eq_zero_of_lt_two]
  | succ n hn ih =>
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rpow_smul_weightedPrimeSum a η n)
      (intervalIntegrable_rpow_smul_weightedPrimeSum_succ a η hn), smul_add, ih,
      integral_rpow_smul_weightedPrimeSum_succ a hη hn, smul_smul, mul_div_cancel₀ _ hη]
    have h := weightedPrimeSum_natCast_succ a n
    push_cast at h
    rw [h, Nat.primesLE_succ]
    split_ifs
    · rw [Finset.sum_insert (Nat.notMem_primesLE n), smul_add, smul_smul,
        rpow_neg_mul_log_div (by positivity)]
      push_cast
      rw [sub_smul]
      abel
    · rw [add_zero, sub_smul]
      abel

/-! ### The limit of the cutoff -/

/-- For weights bounded by `1` on primes and `η > 0`, `t ↦ t^(-1-η) • A(t)` is Bochner integrable
on `(1, ∞)`. -/
theorem integrableOn_rpow_smul_weightedPrimeSum {a : ℕ → E} (ha : ∀ p, p.Prime → ‖a p‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun t ↦ t ^ (-1 - η) • weightedPrimeSum a t) (Ioi 1) := by
  have hg := integrableOn_rpow_mul_one_add_log_sq hη
  have hbound : ∀ t ∈ Ioi (1 : ℝ),
      ‖t ^ (-1 - η) • weightedPrimeSum a t‖ ≤ t ^ (-1 - η) * (1 + log t) ^ 2 := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_smul, norm_of_nonneg (rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_left (norm_weightedPrimeSum_le ha t) (rpow_nonneg ht0.le _)
  have hfi (n : ℕ) :
      IntegrableOn (fun t ↦ t ^ (-1 - η) • weightedPrimeSum a t) (Ioc 1 n) := by
    rcases le_total (n : ℝ) 1 with h | h
    · rw [Ioc_eq_empty (not_lt.2 h)]
      exact integrableOn_empty
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h).1
        (intervalIntegrable_rpow_smul_weightedPrimeSum a η n)
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (∫ t in Ioi 1, t ^ (-1 - η) * (1 + log t) ^ 2) 1 hfi tendsto_natCast_atTop_atTop ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [intervalIntegral.integral_of_le h]
  calc ∫ t in Ioc (1 : ℝ) n, ‖t ^ (-1 - η) • weightedPrimeSum a t‖
      ≤ ∫ t in Ioc (1 : ℝ) n, t ^ (-1 - η) * (1 + log t) ^ 2 :=
        setIntegral_mono_on (hfi n).norm (hg.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
          fun t ht ↦ hbound t ht.1
    _ ≤ ∫ t in Ioi 1, t ^ (-1 - η) * (1 + log t) ^ 2 := by
        refine setIntegral_mono_set hg ?_ Ioc_subset_Ioi_self.eventuallySubset
        refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_)
        exact mul_nonneg (rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _) (sq_nonneg _)

/-- The boundary term `n^(-η) • A(n)` of the partial summation tends to zero. -/
theorem tendsto_rpow_neg_smul_weightedPrimeSum {a : ℕ → E} (ha : ∀ p, p.Prime → ‖a p‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-η) • weightedPrimeSum a n) atTop (𝓝 0) := by
  have hC : Tendsto (fun n : ℕ ↦ exp (η / 2) * (4 / η) ^ 2 * (n : ℝ) ^ (-(η / 2))) atTop
      (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by positivity : 0 < η / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul (exp (η / 2) * (4 / η) ^ 2)
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [norm_smul, norm_of_nonneg (rpow_nonneg hn0.le _)]
  calc (n : ℝ) ^ (-η) * ‖weightedPrimeSum a n‖
      ≤ (n : ℝ) ^ (-η) * (exp (η / 2) * (4 / η) ^ 2 * (n : ℝ) ^ (η / 2)) :=
        mul_le_mul_of_nonneg_left ((norm_weightedPrimeSum_le ha n).trans
          (one_add_log_sq_le hη hn1)) (rpow_nonneg hn0.le _)
    _ = exp (η / 2) * (4 / η) ^ 2 * (n : ℝ) ^ (-(η / 2)) := by
        rw [mul_left_comm, ← rpow_add hn0]
        ring_nf

/-- The weighted prime series, extended by zero to all of `ℕ`, is summable. -/
private theorem summable_indicator_weightedPrimeSeries [CompleteSpace E] {a : ℕ → E}
    (ha : ∀ p, p.Prime → ‖a p‖ ≤ 1) {η : ℝ} (hη : 0 < η) :
    Summable ({p : ℕ | p.Prime}.indicator fun n ↦ (log n / (n : ℝ) ^ (1 + η)) • a n) := by
  refine Summable.of_norm_bounded
    ((summable_nat_rpow.2 (by linarith : -1 - η / 2 < -1)).mul_left (2 / η)) fun n ↦ ?_
  by_cases hn : n.Prime
  · rw [indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hn)]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
    have hlog : 0 ≤ log n := log_nonneg (by exact_mod_cast hn.one_lt.le)
    rw [norm_smul, norm_of_nonneg (div_nonneg hlog (rpow_nonneg hn0.le _))]
    calc log n / (n : ℝ) ^ (1 + η) * ‖a n‖ ≤ log n / (n : ℝ) ^ (1 + η) :=
          mul_le_of_le_one_right (by positivity) (ha n hn)
      _ ≤ (n : ℝ) ^ (η / 2) / (η / 2) / (n : ℝ) ^ (1 + η) :=
          div_le_div_of_nonneg_right (log_le_rpow_div hn0.le (by positivity))
            (rpow_nonneg hn0.le _)
      _ = 2 / η * (n : ℝ) ^ (-1 - η / 2) := by
          rw [show -1 - η / 2 = η / 2 - (1 + η) by ring, rpow_sub hn0]
          field_simp
  · rw [indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hn), norm_zero]
    positivity

/-- **The weighted-prime Mellin identity**: for weights bounded by `1` on primes and `η > 0`,
`Σ_p (log p / p^(1+η)) • a p = η ∫_{t > 1} t^(-1-η) • A(t) dt`. -/
theorem hasSum_weightedPrimeSeries [CompleteSpace E] {a : ℕ → E}
    (ha : ∀ p, p.Prime → ‖a p‖ ≤ 1) {η : ℝ} (hη : 0 < η) :
    HasSum (fun p : Nat.Primes ↦ (log p / (p : ℝ) ^ (1 + η)) • a p)
      (mellinWeightIntegral η (weightedPrimeSum a)) := by
  set f := {p : ℕ | p.Prime}.indicator fun n ↦ (log n / (n : ℝ) ^ (1 + η)) • a n with hf_def
  have hf : Summable f := summable_indicator_weightedPrimeSeries ha hη
  have hpartial (n : ℕ) : ∑ k ∈ Finset.range (n + 1), f k =
      ∑ p ∈ Nat.primesLE n, (log p / (p : ℝ) ^ (1 + η)) • a p := by
    rw [Nat.primesLE_eq_filter_range, Finset.sum_filter]
    exact Finset.sum_congr rfl fun k _ ↦ by simp [hf_def, indicator_apply]
  have h1 : Tendsto (fun n : ℕ ↦ ∑ p ∈ Nat.primesLE n, (log p / (p : ℝ) ^ (1 + η)) • a p)
      atTop (𝓝 (∑' n, f n)) := by
    simpa only [Function.comp_def, hpartial] using
      hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ ↦ ∑ p ∈ Nat.primesLE n, (log p / (p : ℝ) ^ (1 + η)) • a p)
      atTop (𝓝 (mellinWeightIntegral η (weightedPrimeSum a))) := by
    have hI := ((intervalIntegral_tendsto_integral_Ioi 1
      (integrableOn_rpow_smul_weightedPrimeSum ha hη) tendsto_natCast_atTop_atTop).const_smul
        η).add (tendsto_rpow_neg_smul_weightedPrimeSum ha hη)
    rw [add_zero, ← mellinWeightIntegral_def] at hI
    refine hI.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [smul_intervalIntegral_rpow_smul_weightedPrimeSum a hη.ne' hn, sub_add_cancel]
  rw [← tendsto_nhds_unique h1 h2]
  exact hasSum_subtype_iff_indicator.2 hf.hasSum

/-- For weights bounded by `1` on primes and `η > 0`, `Σ_p (log p / p^(1+η)) • a p` is
summable. -/
theorem summable_weightedPrimeSeries [CompleteSpace E] {a : ℕ → E}
    (ha : ∀ p, p.Prime → ‖a p‖ ≤ 1) {η : ℝ} (hη : 0 < η) :
    Summable (fun p : Nat.Primes ↦ (log p / (p : ℝ) ^ (1 + η)) • a p) :=
  summable_subtype_iff_indicator.2 (summable_indicator_weightedPrimeSeries ha hη)

/-- The Mellin identity in `tsum` form. -/
theorem tsum_weightedPrimeSeries [CompleteSpace E] {a : ℕ → E}
    (ha : ∀ p, p.Prime → ‖a p‖ ≤ 1) {η : ℝ} (hη : 0 < η) :
    ∑' p : Nat.Primes, (log p / (p : ℝ) ^ (1 + η)) • a p =
      mellinWeightIntegral η (weightedPrimeSum a) :=
  (hasSum_weightedPrimeSeries ha hη).tsum_eq

end TauCeti
