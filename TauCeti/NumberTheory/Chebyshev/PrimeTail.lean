/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The reciprocal-square logarithmic prime tail

Partial summation and Chebyshev's elementary bound give an absolute tail estimate
for the convergent series with prime terms `log p / p²`. We use `Nat.primesLE`
for finite sums and prime-filtered natural-number sums for infinite tails.
Both strict and inclusive lower cutoffs are available; in particular the inclusive
tail at `2` contains the prime `2`.

The argument is the usual Stieltjes integration by parts against `t⁻²`:
`θ(t) ≤ (log 4) t` gives a tail bounded by `2 log 4 / y`.
-/

public section

open Finset MeasureTheory Filter
open scoped Topology

namespace TauCeti

private theorem sum_prime_log_eq_theta (t : ℝ) :
    ∑ n ∈ Icc 0 ⌊t⌋₊, (if n.Prime then Real.log n else 0) = Chebyshev.theta t := by
  simp [Chebyshev.theta_eq_sum_Icc, sum_filter]

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
    rw [Nat.primesLE_eq_filter_Icc_zero]
    simp only [c, mul_ite, mul_zero, ← sum_filter]
    apply sum_congr
    · ext n
      simp only [mem_filter, mem_Icc, mem_Ioc, zero_le, true_and]
      rw [Nat.floor_lt ha.le]
      tauto
    · intro n _
      simp [div_eq_mul_inv, mul_comm]
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
  · have hempty : (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro p hp hpa
      have hb : 0 ≤ b := by
        by_contra hb
        simp [Nat.floor_of_nonpos (le_of_not_ge hb)] at hp
      have hp_le : (p : ℝ) ≤ b :=
        (Nat.le_floor_iff hb).mp (Nat.mem_primesLE.mp hp).1
      linarith
    rw [hempty, sum_empty]
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

end TauCeti
