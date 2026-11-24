/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import TauCeti.NumberTheory.Chebyshev.PowerTail

/-!
# Prime tails from Chebyshev's bounds

Partial summation and Chebyshev's elementary bound give an absolute tail estimate
for the convergent series with prime terms `log p / p²`. We use `Nat.primesLE`
for finite sums and prime-filtered natural-number sums for infinite tails.
Both strict and inclusive lower cutoffs are available; in particular the inclusive
tail at `2` contains the prime `2`.

The argument is the usual Stieltjes integration by parts against `t⁻²`:
`θ(t) ≤ (log 4) t` gives a tail bounded by `2 log 4 / y`. Dividing by `log 2` then bounds the
unweighted reciprocal-square prime tail `∑_{p > y} 1 / p²` by `4 / y`.

The second half keeps the logarithm in the unweighted tails. Chebyshev's bound
`π(x) ≤ (2 log 4 + 2) x / log x` for every `x > 1` (`primeCounting_floor_le`) and partial
summation against `t ^ (-s)` (`sum_primesLE_rpow_neg_eq`) bound the sum of `p ^ (-s)` over primes
`y < p ≤ b` by `s / (s - 1) · (2 log 4 + 2) · y ^ (1 - s) / log y`, for real `s > 1` and `y > 1`
(`sum_primesLE_rpow_neg_le`); the whole tail, with the sharper constant `s log 4 / (s - 1)`, is
`tsum_prime_rpow_neg_gt_le`. For an integer exponent `k ≥ 2` the constant
`s / (s - 1)` is at most `2`, so `∑_{y < p ≤ b} 1 / p ^ k ≤ 2 (2 log 4 + 2) / (y ^ (k - 1) log y)`
uniformly in `k` (`sum_primesLE_inv_pow_le`). Compared with the elementary bound
`∑_{p > y} 1 / p² ≤ 4 / y`, these save the factor `log y`, which is what the large-prime parts
of geometric sieves need.

## References

* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), proof of
  Theorem 2.20, where the prime count and the tail of `1 / p²` with its logarithm are used.
* M. Bhargava, *The geometric sieve and the density of squarefree values of invariant
  polynomials*, arXiv:1402.0031, proof of Theorem 3.3, display (16), where the tail of
  `1 / p ^ k` is used.
-/

public section

open Finset MeasureTheory Filter
open scoped Topology

namespace TauCeti

private theorem sum_prime_log_eq_theta (t : ℝ) :
    ∑ n ∈ Icc 0 ⌊t⌋₊, (if n.Prime then Real.log n else 0) = Chebyshev.theta t := by
  simp [Chebyshev.theta_eq_sum_Icc, sum_filter]

private theorem sum_prime_indicator_eq_primeCounting (t : ℝ) :
    ∑ n ∈ Icc 0 ⌊t⌋₊, (if n.Prime then (1 : ℝ) else 0) = Nat.primeCounting ⌊t⌋₊ := by
  simp [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]

-- Reindexes the sums produced by partial summation over `(⌊a⌋₊, ⌊b⌋₊]` as prime sums on `(a, b]`.
private theorem sum_Ioc_mul_ite_prime_eq_sum_filter_primesLE {a b : ℝ} (ha : 0 ≤ a)
    (f g : ℕ → ℝ) :
    ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * (if n.Prime then g n else 0) =
      ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)), f p * g p := by
  rw [Nat.primesLE_eq_filter_Icc_zero]
  simp only [mul_ite, mul_zero, ← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem_Ioc, zero_le, true_and]
  rw [Nat.floor_lt ha]
  tauto

private theorem filter_primesLE_floor_gt_eq_empty {a b : ℝ} (hab : ¬ a ≤ b) :
    (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)) = ∅ := by
  refine filter_eq_empty_iff.mpr fun p hp hpa ↦ hab ?_
  have hp' := Nat.mem_primesLE.mp hp
  have hb : 0 ≤ b := by
    by_contra hb
    simp [Nat.floor_of_nonpos (le_of_not_ge hb), hp'.2.ne_zero] at hp'
  exact hpa.le.trans ((Nat.le_floor_iff hb).mp hp'.1)

/-- Partial summation for the logarithmic prime sum on `(a, b]`. -/
theorem sum_primesLE_log_div_sq_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)),
        Real.log p / (p : ℝ) ^ 2 =
      Chebyshev.theta b / b ^ 2 - Chebyshev.theta a / a ^ 2 +
        ∫ t in a..b, 2 * Chebyshev.theta t / t ^ 3 := by
  let c : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n else 0
  have hd (t : ℝ) (ht : t ≠ 0) :
      deriv (fun u : ℝ ↦ (u ^ 2)⁻¹) t = -(2 / t ^ 3) := by
    convert (((hasDerivAt_id' (x := t)).fun_pow 2).inv (pow_ne_zero 2 ht)).deriv using 1
    field_simp
    ring
  have hi : IntervalIntegrable (fun t : ℝ ↦ -(2 / t ^ 3)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have : 0 < t := ha.trans_le ht.1
    fun_prop (disch := positivity)
  have h := sum_mul_eq_sub_sub_integral_mul c ha.le hab
    (f := fun t : ℝ ↦ (t ^ 2)⁻¹)
    (fun t ht ↦ by
      have : 0 < t := ha.trans_le ht.1
      fun_prop (disch := positivity))
    (by
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      exact hi.congr (fun t ht ↦ (hd t (ne_of_gt (ha.trans_le
        ((Set.uIoc_of_le hab) ▸ ht).1.le))).symm))
  have hleft : ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ((n : ℝ) ^ 2)⁻¹ * c n =
      ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)),
        Real.log p / (p : ℝ) ^ 2 := by
    rw [sum_Ioc_mul_ite_prime_eq_sum_filter_primesLE ha.le]
    exact sum_congr rfl fun n _ ↦ by simp [div_eq_mul_inv, mul_comm]
  rw [hleft, sum_prime_log_eq_theta, sum_prime_log_eq_theta,
    ← intervalIntegral.integral_of_le hab] at h
  have heq : (∫ t in a..b, deriv (fun u : ℝ ↦ (u ^ 2)⁻¹) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, c k) = -(∫ t in a..b, 2 * Chebyshev.theta t / t ^ 3) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hd t (ne_of_gt (ha.trans_le ((Set.uIcc_of_le hab) ▸ ht).1)),
      sum_prime_log_eq_theta]
    ring
  rw [h, heq]
  ring

-- Integrability of the remainder in the partial-summation formula.
private theorem intervalIntegrable_two_mul_theta_div_cube {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ 2 * Chebyshev.theta t / t ^ 3) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hint := integrableOn_mul_sum_Icc (m := 0)
    (fun n : ℕ ↦ if n.Prime then Real.log n else 0) ha.le
    (show IntegrableOn (fun t : ℝ ↦ 2 / t ^ 3) (Set.Icc a b) from
      ContinuousOn.integrableOn_Icc (by
        intro t ht
        have : 0 < t := ha.trans_le ht.1
        fun_prop (disch := positivity)))
  simp_rw [sum_prime_log_eq_theta] at hint
  exact hint.congr_fun (fun t _ ↦ by ring) measurableSet_Icc

-- Chebyshev bounds the remainder by an elementary power integral.
private theorem integral_two_mul_theta_div_cube_le {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 2 * Chebyshev.theta t / t ^ 3) ≤
      2 * Real.log 4 * (a⁻¹ - b⁻¹) := by
  have hb : 0 < b := ha.trans_le hab
  have hcont : ContinuousOn (fun t : ℝ ↦ (2 * Real.log 4) / t ^ 2) (Set.Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht ↦ pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  calc
    _ ≤ ∫ t in a..b, (2 * Real.log 4) / t ^ 2 := by
      refine intervalIntegral.integral_mono_on hab
        (intervalIntegrable_two_mul_theta_div_cube ha hab)
        (hcont.intervalIntegrable_of_Icc hab) ?_
      intro t ht
      have ht0 : 0 < t := ha.trans_le ht.1
      calc
        _ ≤ 2 * (Real.log 4 * t) / t ^ 3 := by
          gcongr
          exact Chebyshev.theta_le_log4_mul_x ht0.le
        _ = (2 * Real.log 4) / t ^ 2 := by field_simp
    _ = 2 * Real.log 4 * (a⁻¹ - b⁻¹) := by
      simp_rw [div_eq_mul_inv, ← zpow_natCast, ← zpow_neg]
      norm_num only [Nat.cast_ofNat]
      rw [intervalIntegral.integral_const_mul,
        integral_zpow (n := -2) (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt ha hb⟩)]
      norm_num
      ring

/-- For `a > 0`, the sum of `log p / p²` over primes `a < p ≤ b` is at most
`2 log 4 / a`. -/
theorem sum_primesLE_log_div_sq_le {a b : ℝ} (ha : 0 < a) :
    ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)),
        Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / a := by
  by_cases hab : a ≤ b
  · have hb : 0 < b := ha.trans_le hab
    -- Abel summation reduces the finite tail to a Chebyshev boundary term and integral.
    have hbound := integral_two_mul_theta_div_cube_le ha hab
    rw [sum_primesLE_log_div_sq_eq ha hab]
    have htheta := Chebyshev.theta_le_log4_mul_x hb.le
    have _ := Chebyshev.theta_nonneg a
    have _ : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have htop : Chebyshev.theta b / b ^ 2 ≤ Real.log 4 / b := by
      apply (div_le_iff₀ (sq_pos_of_pos hb)).2
      convert htheta using 1
      field_simp
    have hbottom : 0 ≤ Chebyshev.theta a / a ^ 2 := by positivity
    have hlogb : 0 ≤ Real.log 4 / b := by positivity
    calc
      _ ≤ Real.log 4 / b + 2 * Real.log 4 * (a⁻¹ - b⁻¹) := by linarith
      _ = 2 * Real.log 4 / a - Real.log 4 / b := by ring
      _ ≤ 2 * Real.log 4 / a := sub_le_self _ hlogb
  · rw [filter_primesLE_floor_gt_eq_empty hab, sum_empty]
    positivity

/-- For `y > 0`, the sum of `log p / p²` over any finite set of primes `p ≥ y`
is at most `2 log 4 / y`. -/
theorem sum_log_div_sq_le_of_prime {s : Finset ℕ} {y : ℝ} (hy : 0 < y)
    (hs : ∀ p ∈ s, p.Prime) (hys : ∀ p ∈ s, y ≤ (p : ℝ)) :
    ∑ p ∈ s, Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / y := by
  have hstrict (a : ℝ) (ha : 0 < a) (hay : a < y) :
      ∑ p ∈ s, Real.log p / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / a := by
    apply le_trans ?_ (sum_primesLE_log_div_sq_le (b := ((s.sup id : ℕ) : ℝ)) ha)
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [mem_filter, Nat.mem_primesLE, Nat.floor_natCast]
      exact ⟨⟨le_sup (f := id) hp, hs p hp⟩, hay.trans_le (hys p hp)⟩
    · intro p _ _
      positivity
  have hlim : Tendsto (fun a : ℝ ↦ 2 * Real.log 4 / a) (𝓝[<] y)
      (𝓝 (2 * Real.log 4 / y)) :=
    (continuousAt_const.div continuousAt_id hy.ne').tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hy] with a ha
  exact hstrict a ha.1 ha.2

/-- The prime-supported series with terms `log p / p²` is summable. -/
theorem summable_prime_log_div_sq :
    Summable (fun n : ℕ ↦ if n.Prime then Real.log n / (n : ℝ) ^ 2 else 0) := by
  apply summable_of_sum_le (c := Real.log 4)
  · intro n
    positivity
  · intro s
    rw [← sum_filter]
    convert sum_log_div_sq_le_of_prime (y := 2) (by norm_num)
      (s := s.filter Nat.Prime) (by simp) (by
        intro p hp
        exact_mod_cast (mem_filter.mp hp).2.two_le) using 1
    norm_num

/-- The series with terms `log p / p²` over primes satisfying a decidable predicate `P`
is summable. -/
theorem summable_prime_log_div_sq_of_pred (P : ℕ → Prop) [DecidablePred P] :
    Summable (fun n : ℕ ↦ if n.Prime ∧ P n then Real.log n / (n : ℝ) ^ 2 else 0) := by
  refine (summable_prime_log_div_sq.indicator {n : ℕ | P n}).congr fun n ↦ ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> tauto

/-- The series with terms `log p / p²` over primes `p ≥ y` is summable. -/
theorem summable_prime_log_div_sq_ge (y : ℝ) :
    Summable (fun n : ℕ ↦ if n.Prime ∧ y ≤ (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) :=
  summable_prime_log_div_sq_of_pred (fun n ↦ y ≤ (n : ℝ))

/-- The series with terms `log p / p²` over primes `p > y` is summable. -/
theorem summable_prime_log_div_sq_gt (y : ℝ) :
    Summable (fun n : ℕ ↦ if n.Prime ∧ y < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) :=
  summable_prime_log_div_sq_of_pred (fun n ↦ y < (n : ℝ))

/-- For `y > 0`, the sum of `log p / p²` over primes `p ≥ y` is at most
`2 log 4 / y`, including a prime at the lower endpoint. -/
theorem tsum_prime_log_div_sq_ge_le {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, if n.Prime ∧ y ≤ (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) ≤
      2 * Real.log 4 / y := by
  apply Real.tsum_le_of_sum_le
  · intro n
    positivity
  · intro s
    rw [← sum_filter]
    exact sum_log_div_sq_le_of_prime hy
      (fun p hp ↦ (mem_filter.mp hp).2.1) (fun p hp ↦ (mem_filter.mp hp).2.2)

/-- For `y > 0`, the sum of `log p / p²` over primes `p > y` is at most
`2 log 4 / y`. -/
theorem tsum_prime_log_div_sq_gt_le {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, if n.Prime ∧ y < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) ≤
      2 * Real.log 4 / y := by
  apply Real.tsum_le_of_sum_le
  · intro n
    positivity
  · intro s
    rw [← sum_filter]
    exact sum_log_div_sq_le_of_prime hy
      (fun p hp ↦ (mem_filter.mp hp).2.1) (fun p hp ↦ (mem_filter.mp hp).2.2.le)

/-- At a prime lower endpoint, the inclusive and strict tails differ by exactly its term. -/
theorem tsum_prime_log_div_sq_ge_eq {p : ℕ} (hp : p.Prime) :
    (∑' n : ℕ, if n.Prime ∧ (p : ℝ) ≤ n then Real.log n / (n : ℝ) ^ 2 else 0) =
      Real.log p / (p : ℝ) ^ 2 +
        ∑' n : ℕ, if n.Prime ∧ (p : ℝ) < n then Real.log n / (n : ℝ) ^ 2 else 0 := by
  rw [(summable_prime_log_div_sq_ge p).tsum_eq_add_tsum_ite p]
  simp only [hp, le_refl, and_self, ite_true]
  congr 1
  apply tsum_congr
  intro n
  split_ifs <;> simp_all <;> grind

/-- Removing `(a, b]` from a strict tail leaves the strict tail at `b`.
The upper endpoint occurs only in the finite interval sum. -/
theorem sum_primesLE_log_div_sq_add_tsum_gt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)),
      Real.log p / (p : ℝ) ^ 2) +
      (∑' n : ℕ, if n.Prime ∧ b < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) =
      ∑' n : ℕ, if n.Prime ∧ a < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0 := by
  have hdiff := (summable_prime_log_div_sq_gt a).tsum_sub (summable_prime_log_div_sq_gt b)
  have hfinite : (∑' n : ℕ,
      ((if n.Prime ∧ a < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) -
      (if n.Prime ∧ b < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0))) =
      ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)),
        Real.log p / (p : ℝ) ^ 2 := by
    rw [tsum_eq_sum (s := (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)))]
    · apply sum_congr rfl
      intro n hn
      obtain ⟨hn, han⟩ := mem_filter.mp hn
      obtain ⟨hnb, hn⟩ := Nat.mem_primesLE.mp hn
      have hnb' := (Nat.le_floor_iff (ha.trans hab)).mp hnb
      simp [hn, han, not_lt_of_ge hnb']
    · intro n hn
      simp only [mem_filter, Nat.mem_primesLE, Nat.le_floor_iff (ha.trans hab)] at hn
      split_ifs <;> grind
  linarith

private theorem prime_inv_sq_gt_le_mul_log_div_sq (y : ℝ) (n : ℕ) :
    (if n.Prime ∧ y < (n : ℝ) then ((n : ℝ) ^ 2)⁻¹ else 0) ≤
      (Real.log 2)⁻¹ * (if n.Prime ∧ y < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  split_ifs with hn
  · have hle : Real.log 2 ≤ Real.log n := Real.log_le_log zero_lt_two (mod_cast hn.1.two_le)
    have h1 : (1 : ℝ) ≤ (Real.log 2)⁻¹ * Real.log n := (le_inv_mul_iff₀ hlog2).mpr (by linarith)
    calc ((n : ℝ) ^ 2)⁻¹ = 1 * ((n : ℝ) ^ 2)⁻¹ := (one_mul _).symm
      _ ≤ ((Real.log 2)⁻¹ * Real.log n) * ((n : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (Real.log 2)⁻¹ * (Real.log n / (n : ℝ) ^ 2) := by ring
  · simp

/-- The series with terms `1 / p²` over primes `p > y` is summable. -/
theorem summable_prime_inv_sq_gt (y : ℝ) :
    Summable (fun n : ℕ ↦ if n.Prime ∧ y < (n : ℝ) then ((n : ℝ) ^ 2)⁻¹ else 0) :=
  ((summable_prime_log_div_sq_gt y).mul_left (Real.log 2)⁻¹).of_nonneg_of_le
    (fun n ↦ by split_ifs <;> positivity) (prime_inv_sq_gt_le_mul_log_div_sq y)

/-- For `y > 0`, the sum of `1 / p²` over primes `p > y` is at most `4 / y`. -/
theorem tsum_prime_inv_sq_gt_le {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, if n.Prime ∧ y < (n : ℝ) then ((n : ℝ) ^ 2)⁻¹ else 0) ≤ 4 / y := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc (∑' n : ℕ, if n.Prime ∧ y < (n : ℝ) then ((n : ℝ) ^ 2)⁻¹ else 0)
      ≤ ∑' n : ℕ, (Real.log 2)⁻¹ *
          (if n.Prime ∧ y < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) :=
        (summable_prime_inv_sq_gt y).tsum_le_tsum (prime_inv_sq_gt_le_mul_log_div_sq y)
          ((summable_prime_log_div_sq_gt y).mul_left _)
    _ = (Real.log 2)⁻¹ * ∑' n : ℕ,
          (if n.Prime ∧ y < (n : ℝ) then Real.log n / (n : ℝ) ^ 2 else 0) := tsum_mul_left
    _ ≤ (Real.log 2)⁻¹ * (2 * Real.log 4 / y) :=
        mul_le_mul_of_nonneg_left (tsum_prime_log_div_sq_gt_le hy) (inv_nonneg.mpr hlog2.le)
    _ = 4 / y := by
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          have h22 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
          rw [h22, Real.log_pow]
          ring
        rw [h4]
        field_simp [hlog2.ne']
        ring

/-! ### Chebyshev's bound for `π(x)` and prime tails of `p ^ (-s)` -/

/-- Partial summation for the sum of `p ^ (-s)` over primes `a < p ≤ b`, against the
prime-counting function. -/
theorem sum_primesLE_rpow_neg_eq (s : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)), (p : ℝ) ^ (-s) =
      b ^ (-s) * Nat.primeCounting ⌊b⌋₊ - a ^ (-s) * Nat.primeCounting ⌊a⌋₊ +
        s * ∫ t in a..b, t ^ (-s - 1) * Nat.primeCounting ⌊t⌋₊ := by
  let c : ℕ → ℝ := fun n ↦ if n.Prime then 1 else 0
  have hc (t : ℝ) : ∑ k ∈ Icc 0 ⌊t⌋₊, c k = Nat.primeCounting ⌊t⌋₊ :=
    sum_prime_indicator_eq_primeCounting t
  have hd (t : ℝ) : deriv (fun u : ℝ ↦ u ^ (-s)) t = -s * t ^ (-s - 1) :=
    Real.deriv_rpow_const t (-s)
  have h := sum_mul_eq_sub_sub_integral_mul c ha.le hab (f := fun t : ℝ ↦ t ^ (-s))
    (fun t ht ↦
      (Real.hasDerivAt_rpow_const (Or.inl (ha.trans_le ht.1).ne')).differentiableAt)
    (by
      rw [show deriv (fun u : ℝ ↦ u ^ (-s)) = fun t ↦ -s * t ^ (-s - 1) from funext hd]
      refine ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
      have : t ≠ 0 := (ha.trans_le ht.1).ne'
      fun_prop (disch := exact Or.inl this))
  have hleft : ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℝ) ^ (-s) * c n =
      ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)), (p : ℝ) ^ (-s) := by
    simp only [c, sum_Ioc_mul_ite_prime_eq_sum_filter_primesLE ha.le, mul_one]
  rw [hleft, hc, hc, ← intervalIntegral.integral_of_le hab] at h
  have heq : (∫ t in a..b, deriv (fun u : ℝ ↦ u ^ (-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =
      -(s * ∫ t in a..b, t ^ (-s - 1) * Nat.primeCounting ⌊t⌋₊) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [hd, hc]
    ring
  rw [h, heq]
  ring

-- On `t ≥ a > 1`, Chebyshev's bound gives `t ^ (-s - 1) π(t) ≤ ((2 log 4 + 2) / log a) t ^ (-s)`.
private theorem rpow_sub_one_mul_primeCounting_le (s : ℝ) {a t : ℝ} (ha : 1 < a) (hat : a ≤ t) :
    t ^ (-s - 1) * Nat.primeCounting ⌊t⌋₊ ≤ (2 * Real.log 4 + 2) / Real.log a * t ^ (-s) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have ht0 : 0 < t := ha0.trans_le hat
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogt : Real.log a ≤ Real.log t := Real.log_le_log ha0 hat
  calc t ^ (-s - 1) * Nat.primeCounting ⌊t⌋₊ ≤
        t ^ (-s - 1) * ((2 * Real.log 4 + 2) * t / Real.log t) :=
        mul_le_mul_of_nonneg_left (primeCounting_floor_le (ha.trans_le hat))
          (by positivity)
    _ ≤ t ^ (-s - 1) * ((2 * Real.log 4 + 2) * t / Real.log a) := by gcongr
    _ = (2 * Real.log 4 + 2) / Real.log a * (t ^ (-s - 1) * t) := by ring
    _ = (2 * Real.log 4 + 2) / Real.log a * t ^ (-s) := by
        rw [← Real.rpow_add_one ht0.ne', sub_add_cancel]

-- Integrating the pointwise bound bounds the remainder of the partial-summation formula.
private theorem integral_rpow_sub_one_mul_primeCounting_le {s a b : ℝ} (hs : 1 < s) (ha : 1 < a)
    (hab : a ≤ b) :
    ∫ t in a..b, t ^ (-s - 1) * Nat.primeCounting ⌊t⌋₊ ≤
      (2 * Real.log 4 + 2) / Real.log a * ((a ^ (1 - s) - b ^ (1 - s)) / (s - 1)) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hcont : ContinuousOn
      (fun t : ℝ ↦ (2 * Real.log 4 + 2) / Real.log a * t ^ (-s)) (Set.Icc a b) :=
    fun t ht ↦ by
      have : t ≠ 0 := (ha0.trans_le ht.1).ne'
      fun_prop (disch := exact Or.inl this)
  have hcont' : ContinuousOn (fun t : ℝ ↦ t ^ (-s - 1)) (Set.Icc a b) :=
    fun t ht ↦ by
      have : t ≠ 0 := (ha0.trans_le ht.1).ne'
      fun_prop (disch := exact Or.inl this)
  have hlhs := integrableOn_mul_sum_Icc (m := 0)
    (fun n : ℕ ↦ if n.Prime then (1 : ℝ) else 0) ha0.le hcont'.integrableOn_Icc
  simp_rw [sum_prime_indicator_eq_primeCounting] at hlhs
  calc _ ≤ ∫ t in a..b, (2 * Real.log 4 + 2) / Real.log a * t ^ (-s) := by
        refine intervalIntegral.integral_mono_on hab ?_ (hcont.intervalIntegrable_of_Icc hab)
          fun t ht ↦ rpow_sub_one_mul_primeCounting_le s ha ht.1
        rwa [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr
          ⟨by linarith, Set.notMem_uIcc_of_lt ha0 hb0⟩), show -s + 1 = 1 - s by ring]
        congr 1
        rw [div_eq_div_iff (by linarith) (by linarith)]
        ring

/-- For `s > 1` and `a > 1`, the sum of `p ^ (-s)` over primes `a < p ≤ b` is at most
`s / (s - 1) · (2 log 4 + 2) · a ^ (1 - s) / log a`, uniformly in `b`. -/
theorem sum_primesLE_rpow_neg_le {s a : ℝ} (hs : 1 < s) (ha : 1 < a) (b : ℝ) :
    ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)), (p : ℝ) ^ (-s) ≤
      s / (s - 1) * (2 * Real.log 4 + 2) * a ^ (1 - s) / Real.log a := by
  set C := 2 * Real.log 4 + 2
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hloga : 0 < Real.log a := Real.log_pos ha
  have _ : 0 < C := by positivity
  have _ : 0 < s - 1 := sub_pos.mpr hs
  by_cases hab : a ≤ b
  · have hb0 : 0 < b := ha0.trans_le hab
    -- The boundary term at `b` is at most `(C / log a) b ^ (1 - s)`.
    have htop : b ^ (-s) * Nat.primeCounting ⌊b⌋₊ ≤ C / Real.log a * b ^ (1 - s) :=
      calc b ^ (-s) * Nat.primeCounting ⌊b⌋₊ =
            b ^ (-s - 1) * Nat.primeCounting ⌊b⌋₊ * b := by
            rw [mul_right_comm, ← Real.rpow_add_one hb0.ne', sub_add_cancel]
        _ ≤ C / Real.log a * b ^ (-s) * b :=
            mul_le_mul_of_nonneg_right (rpow_sub_one_mul_primeCounting_le s ha hab) hb0.le
        _ = C / Real.log a * b ^ (1 - s) := by
            rw [mul_assoc, ← Real.rpow_add_one hb0.ne', neg_add_eq_sub]
    have hbot : 0 ≤ a ^ (-s) * Nat.primeCounting ⌊a⌋₊ := by positivity
    have hB : 0 ≤ C / Real.log a * b ^ (1 - s) / (s - 1) := by positivity
    rw [sum_primesLE_rpow_neg_eq s ha0 hab]
    calc _ ≤ C / Real.log a * b ^ (1 - s) - 0 +
          s * (C / Real.log a * ((a ^ (1 - s) - b ^ (1 - s)) / (s - 1))) := by
          gcongr
          exact integral_rpow_sub_one_mul_primeCounting_le hs ha hab
      _ = s / (s - 1) * C * a ^ (1 - s) / Real.log a -
          C / Real.log a * b ^ (1 - s) / (s - 1) := by
          field_simp
          ring
      _ ≤ _ := sub_le_self _ hB
  · -- For `b < a` there is no prime in `(a, b]`.
    rw [filter_primesLE_floor_gt_eq_empty hab, sum_empty]
    positivity

/-- For `s > 1`, the series with terms `p ^ (-s)` over primes `p > y` is summable. -/
theorem summable_prime_rpow_neg_gt {s : ℝ} (hs : 1 < s) (y : ℝ) :
    Summable (fun n : ℕ ↦ if n.Prime ∧ y < (n : ℝ) then (n : ℝ) ^ (-s) else 0) :=
  (Real.summable_nat_rpow.mpr (neg_lt_neg hs)).of_nonneg_of_le
    (fun n ↦ by split_ifs <;> positivity) (fun n ↦ by split_ifs <;> simp [Real.rpow_nonneg])

/-- For an integer exponent `k ≥ 2` and `a > 1`, the sum of `1 / p ^ k` over primes
`a < p ≤ b` is at most `2 (2 log 4 + 2) / (a ^ (k - 1) log a)`, with a constant independent of
`k`, `a` and `b`. -/
theorem sum_primesLE_inv_pow_le {k : ℕ} (hk : 2 ≤ k) {a : ℝ} (ha : 1 < a) (b : ℝ) :
    ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)), ((p : ℝ) ^ k)⁻¹ ≤
      2 * (2 * Real.log 4 + 2) / (a ^ (k - 1) * Real.log a) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have h := sum_primesLE_rpow_neg_le hk' ha b
  simp only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast] at h
  have hpow : a ^ (1 - (k : ℝ)) = (a ^ (k - 1))⁻¹ := by
    rw [show (1 : ℝ) - k = -((k - 1 : ℕ) : ℝ) by push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring,
      Real.rpow_neg ha0.le, Real.rpow_natCast]
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hfrac : (k : ℝ) / (k - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hD : 0 ≤ (2 * Real.log 4 + 2) / (a ^ (k - 1) * Real.log a) := by
    have := Real.log_pos ha
    positivity
  calc _ ≤ _ := h
    _ = (k : ℝ) / (k - 1) * ((2 * Real.log 4 + 2) / (a ^ (k - 1) * Real.log a)) := by
      rw [hpow]
      ring
    _ ≤ 2 * ((2 * Real.log 4 + 2) / (a ^ (k - 1) * Real.log a)) :=
      mul_le_mul_of_nonneg_right hfrac hD
    _ = _ := by ring

end TauCeti
