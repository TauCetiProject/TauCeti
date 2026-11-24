/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Ramanujan sums

For `q : ℕ` and `n : ℤ`, the Ramanujan sum is the sum of `e(bn/q) = exp(2πibn/q)` over the
residues `0 ≤ b < q` coprime to `q`:
`c_q(n) = ∑_{0 ≤ b < q, gcd(b, q) = 1} e(bn/q)`.

It is the value at `n` of the sum of the primitive `q`-th roots of unity, and the arithmetic
factor of the major-arc contribution in the circle method: the singular series of the
three-primes problem is `∑_q μ(q) c_q(N) / φ(q)³`.

## Main results

* `TauCeti.sum_range_exp_two_pi_I_mul_div`: the complete sum `∑_{0 ≤ b < q} e(bn/q)` is `q` if
  `q ∣ n` and `0` otherwise.
* `TauCeti.sum_divisors_ramanujanSum`: grouping `0 ≤ b < q` by `gcd(b, q)`,
  `∑_{d ∣ q} c_d(n) = q · 1_{q ∣ n}`.
* `TauCeti.ramanujanSum_eq_sum_divisors`: Möbius inversion of the previous identity,
  `c_q(n) = ∑_{d ∣ q, d ∣ n} d μ(q/d)`; in particular `c_q(n)` is an integer
  (`TauCeti.ramanujanSum_eq_intCast_sum_divisors`).
* `TauCeti.ramanujanSum_mul`: `c_q(n)` is multiplicative in `q`.
* `TauCeti.ramanujanSum_zero_right`, `TauCeti.ramanujanSum_of_gcd_eq_one`: `c_q(0) = φ(q)`, and
  `c_q(n) = μ(q)` when `gcd(n, q) = 1`.
* `TauCeti.ramanujanSum_prime_pow_succ`, `TauCeti.ramanujanSum_prime`,
  `TauCeti.ramanujanSum_prime_pow_eq_zero`: the values at prime powers; `c_p(n)` is `p - 1` or
  `-1` according as `p ∣ n`, and `c_{p^k}(n) = 0` for `k ≥ 2` and `p ∤ n`.
* `TauCeti.norm_ramanujanSum_le`: `|c_q(n)| ≤ gcd(n, q)`.

The sum is over `Finset.range q`, so `c_0(n) = 0`; every statement holds for all `q : ℕ`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer, 2000, Chapter 26.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., Oxford
  University Press, 2008, §16.6.
-/

public section

noncomputable section

open Complex Finset
open scoped Real ArithmeticFunction.Moebius

namespace TauCeti

/-! ### The complete exponential sum -/

/-- The complete exponential sum `∑_{0 ≤ b < q} e(bn/q)` is `q` if `q ∣ n` and `0` otherwise. -/
theorem sum_range_exp_two_pi_I_mul_div (q : ℕ) (n : ℤ) :
    ∑ b ∈ range q, Complex.exp (2 * π * I * ((b * n / q : ℝ) : ℂ)) =
      if (q : ℤ) ∣ n then (q : ℂ) else 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hprim := Complex.isPrimitiveRoot_exp q hq
  have hterm (b : ℕ) : Complex.exp (2 * π * I * ((b * n / q : ℝ) : ℂ)) =
      (Complex.exp (2 * π * I / q) ^ n) ^ b := by
    rw [← Complex.exp_intCast_mul, ← Complex.exp_natCast_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  split_ifs with h
  · simp [(hprim.zpow_eq_one_iff_dvd n).2 h]
  · have hζ : Complex.exp (2 * π * I / q) ^ n ≠ 1 := fun h' =>
      h ((hprim.zpow_eq_one_iff_dvd n).1 h')
    rw [geom_sum_eq hζ, ← zpow_natCast, ← zpow_mul,
      (hprim.zpow_eq_one_iff_dvd _).2 (dvd_mul_left _ _), sub_self, zero_div]

/-! ### Ramanujan sums -/

/-- The Ramanujan sum `c_q(n) = ∑_{0 ≤ b < q, gcd(b, q) = 1} e(bn/q)`, where
`e(α) = exp(2πiα)`. It vanishes for `q = 0`. -/
def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ b ∈ range q with q.Coprime b, Complex.exp (2 * π * I * ((b * n / q : ℝ) : ℂ))

/-- Unfolding `ramanujanSum`. -/
theorem ramanujanSum_def (q : ℕ) (n : ℤ) :
    ramanujanSum q n =
      ∑ b ∈ range q with q.Coprime b, Complex.exp (2 * π * I * ((b * n / q : ℝ) : ℂ)) :=
  (rfl)

/-- `c_0(n) = 0`: the range `0 ≤ b < 0` is empty. -/
@[simp]
theorem ramanujanSum_zero_left (n : ℤ) : ramanujanSum 0 n = 0 := by
  simp [ramanujanSum_def]

/-- `c_q(0) = φ(q)`. -/
@[simp]
theorem ramanujanSum_zero_right (q : ℕ) : ramanujanSum q 0 = q.totient := by
  simp [ramanujanSum_def, Nat.totient]

/-- The terms `0 ≤ b < q` with `gcd(q, b) = d` contribute the Ramanujan sum `c_{q/d}(n)`. -/
private theorem ramanujanSum_div_eq_sum_filter_gcd {q d : ℕ} (hd : d ∣ q) (hq : q ≠ 0) (n : ℤ) :
    ramanujanSum (q / d) n =
      ∑ b ∈ range q with q.gcd b = d, Complex.exp (2 * π * I * ((b * n / q : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ := hd
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hq
  rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd0), ramanujanSum_def]
  refine Finset.sum_nbij' (d * ·) (· / d) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [mem_filter, mem_range] at hb ⊢
    refine ⟨(Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hd0)).2 hb.1, ?_⟩
    rw [Nat.gcd_mul_left, hb.2, mul_one]
  · intro b hb
    simp only [mem_filter, mem_range] at hb ⊢
    obtain ⟨c, rfl⟩ : d ∣ b := hb.2 ▸ Nat.gcd_dvd_right _ _
    rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hd0)]
    refine ⟨(Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hd0)).1 hb.1, ?_⟩
    rw [Nat.gcd_mul_left] at hb
    exact (mul_eq_left₀ hd0).1 hb.2
  · intro b _
    simp [hd0]
  · intro b hb
    simp only [mem_filter, mem_range] at hb
    exact Nat.mul_div_cancel' (hb.2 ▸ Nat.gcd_dvd_right _ _)
  · intro b _
    congr 2
    push_cast
    field_simp

/-- Grouping `0 ≤ b < q` according to `gcd(b, q)`: `∑_{d ∣ q} c_d(n) = q · 1_{q ∣ n}`. -/
theorem sum_divisors_ramanujanSum (q : ℕ) (n : ℤ) :
    ∑ d ∈ q.divisors, ramanujanSum d n = if (q : ℤ) ∣ n then (q : ℂ) else 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rw [← sum_range_exp_two_pi_I_mul_div, ← Nat.sum_div_divisors,
    ← Finset.sum_fiberwise_of_maps_to (s := range q) (t := q.divisors) (g := q.gcd)
      fun b _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hq⟩]
  exact Finset.sum_congr rfl fun d hd =>
    ramanujanSum_div_eq_sum_filter_gcd (Nat.dvd_of_mem_divisors hd) hq n

/-- The arithmetic function `d ↦ d · 1_{d ∣ n}`, whose Dirichlet convolution with `μ` is
`q ↦ c_q(n)`. -/
private def dvdWeight (n : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun d => if (d : ℤ) ∣ n then (d : ℂ) else 0, by simp⟩

private theorem dvdWeight_apply (n : ℤ) (d : ℕ) :
    dvdWeight n d = if (d : ℤ) ∣ n then (d : ℂ) else 0 :=
  (rfl)

private theorem isMultiplicative_dvdWeight (n : ℤ) : (dvdWeight n).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [dvdWeight_apply], fun {a b} _ _ hab => ?_⟩
  have key : ((a * b : ℕ) : ℤ) ∣ n ↔ (a : ℤ) ∣ n ∧ (b : ℤ) ∣ n := by
    simp only [Int.natCast_dvd]
    exact ⟨fun h => ⟨(Dvd.intro _ rfl).trans h, (Dvd.intro_left _ rfl).trans h⟩,
      fun h => hab.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  simp only [dvdWeight_apply, key]
  by_cases ha : (a : ℤ) ∣ n <;> by_cases hb : (b : ℤ) ∣ n <;> simp [ha, hb]

/-- `q ↦ c_q(n)` is the Dirichlet convolution of `μ` with `d ↦ d · 1_{d ∣ n}`. -/
private theorem ramanujanSum_eq_moebius_mul (q : ℕ) (n : ℤ) :
    ramanujanSum q n = ((μ : ArithmeticFunction ℂ) * dvdWeight n) q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  rw [ArithmeticFunction.mul_apply]
  refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.1
    (fun q _ => sum_divisors_ramanujanSum q n) q hq).symm.trans ?_
  simp [dvdWeight_apply]

/-- The convolution `μ * dvdWeight n` at `q`, written as a sum over the divisors of `q`. -/
private theorem ramanujanSum_eq_sum_divisors_dvdWeight (q : ℕ) (n : ℤ) :
    ramanujanSum q n = ∑ d ∈ q.divisors, (μ (q / d) : ℂ) * dvdWeight n d := by
  rw [ramanujanSum_eq_moebius_mul, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ : ArithmeticFunction ℂ) a * dvdWeight n b)]
  simp only [ArithmeticFunction.intCoe_apply]

/-- The divisor formula `c_q(n) = ∑_{d ∣ q, d ∣ n} d μ(q/d)`. -/
theorem ramanujanSum_eq_sum_divisors (q : ℕ) (n : ℤ) :
    ramanujanSum q n = ∑ d ∈ q.divisors with ((d : ℕ) : ℤ) ∣ n, (d : ℂ) * μ (q / d) := by
  rw [ramanujanSum_eq_sum_divisors_dvdWeight, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [dvdWeight_apply]
  split_ifs <;> ring

/-- `c_q(n)` is an integer. -/
theorem ramanujanSum_eq_intCast_sum_divisors (q : ℕ) (n : ℤ) :
    ramanujanSum q n =
      ((∑ d ∈ q.divisors with ((d : ℕ) : ℤ) ∣ n, (d : ℤ) * μ (q / d) : ℤ) : ℂ) := by
  exact_mod_cast ramanujanSum_eq_sum_divisors q n

/-- `c_q(-n) = c_q(n)`. -/
@[simp]
theorem ramanujanSum_neg (q : ℕ) (n : ℤ) : ramanujanSum q (-n) = ramanujanSum q n := by
  simp only [ramanujanSum_eq_sum_divisors, Int.dvd_neg]

/-- The Ramanujan sum is multiplicative in the modulus. -/
theorem ramanujanSum_mul {q r : ℕ} (h : q.Coprime r) (n : ℤ) :
    ramanujanSum (q * r) n = ramanujanSum q n * ramanujanSum r n := by
  simp only [ramanujanSum_eq_moebius_mul]
  exact (ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (isMultiplicative_dvdWeight n)).map_mul_of_coprime h

/-- `c_q(n) = μ(q)` when `gcd(n, q) = 1`. -/
theorem ramanujanSum_of_gcd_eq_one {q : ℕ} {n : ℤ} (h : Int.gcd n q = 1) :
    ramanujanSum q n = μ q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rw [ramanujanSum_eq_sum_divisors, Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    simp only [mem_filter, Nat.mem_divisors] at hd
    refine absurd ?_ hd1
    have : (d : ℤ) ∣ Int.gcd n q := Int.dvd_coe_gcd hd.2 (Int.natCast_dvd_natCast.2 hd.1.1)
    rw [h] at this
    exact_mod_cast Int.eq_one_of_dvd_one (Int.natCast_nonneg d) this
  · intro h1
    simp [hq] at h1

/-- `c_q(1) = μ(q)`. -/
@[simp]
theorem ramanujanSum_one_right (q : ℕ) : ramanujanSum q 1 = μ q :=
  ramanujanSum_of_gcd_eq_one (by simp)

/-- `c_1(n) = 1`. -/
@[simp]
theorem ramanujanSum_one_left (n : ℤ) : ramanujanSum 1 n = 1 := by
  simp [ramanujanSum_of_gcd_eq_one (Int.gcd_one_right n)]

/-! ### Prime powers -/

/-- `c_{p^{k+1}}(n) = p^{k+1} · 1_{p^{k+1} ∣ n} - p^k · 1_{p^k ∣ n}`. -/
theorem ramanujanSum_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) (n : ℤ) :
    ramanujanSum (p ^ (k + 1)) n =
      (if (p : ℤ) ^ (k + 1) ∣ n then (p : ℂ) ^ (k + 1) else 0) -
        if (p : ℤ) ^ k ∣ n then (p : ℂ) ^ k else 0 := by
  -- Only the divisors `p ^ (k + 1)` and `p ^ k` contribute: `μ (p ^ j) = 0` for `j ≥ 2`.
  have hvanish : ∀ i < k, μ (p ^ (k + 1) / p ^ i) = 0 := fun i hi => by
    rw [Nat.pow_div (by omega) hp.pos, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k + 1 - i ≠ 1 by omega]
  have htop : μ (p ^ (k + 1) / p ^ (k + 1)) = 1 := by
    rw [Nat.div_self (pow_pos hp.pos _), ArithmeticFunction.moebius_apply_one]
  have hnext : μ (p ^ (k + 1) / p ^ k) = -1 := by
    rw [Nat.pow_div k.le_succ hp.pos, show k + 1 - k = 1 by omega, pow_one,
      ArithmeticFunction.moebius_apply_prime hp]
  rw [ramanujanSum_eq_sum_divisors_dvdWeight, Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero fun i hi => by rw [hvanish i (mem_range.1 hi), Int.cast_zero, zero_mul],
    htop, hnext, dvdWeight_apply, dvdWeight_apply]
  push_cast
  ring

/-- `c_p(n)` is `p - 1` if `p ∣ n` and `-1` otherwise. -/
theorem ramanujanSum_prime {p : ℕ} (hp : p.Prime) (n : ℤ) :
    ramanujanSum p n = if (p : ℤ) ∣ n then (p : ℂ) - 1 else -1 := by
  simpa [apply_ite (· - (1 : ℂ))] using ramanujanSum_prime_pow_succ hp 0 n

/-- `c_{p^k}(n) = 0` for `k ≥ 2` and `p ∤ n`. -/
theorem ramanujanSum_prime_pow_eq_zero {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) {n : ℤ}
    (hn : ¬(p : ℤ) ∣ n) : ramanujanSum (p ^ k) n = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : ¬(p : ℤ) ^ j ∣ n := fun h => hn ((dvd_pow_self _ (by omega)).trans h)
  have hj1 : ¬(p : ℤ) ^ (j + 1) ∣ n := fun h => hj ((pow_dvd_pow _ j.le_succ).trans h)
  simp [ramanujanSum_prime_pow_succ hp, hj, hj1]

/-! ### The bound `|c_q(n)| ≤ gcd(n, q)` -/

private theorem norm_ramanujanSum_prime_pow_le {p : ℕ} (hp : p.Prime) (k : ℕ) (n : ℤ) :
    ‖ramanujanSum (p ^ k) n‖ ≤ Int.gcd n (p ^ k : ℕ) := by
  rcases k with _ | k
  · simp
  have hgcd_pos : 0 < Int.gcd n (p ^ (k + 1) : ℕ) :=
    Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast (pow_pos hp.pos _).ne')
  have hle {m : ℕ} (hm : (m : ℤ) ∣ n) (hmq : m ∣ p ^ (k + 1)) :
      (m : ℝ) ≤ Int.gcd n (p ^ (k + 1) : ℕ) := by
    exact_mod_cast Nat.le_of_dvd hgcd_pos
      (Int.natCast_dvd_natCast.1 (Int.dvd_coe_gcd hm (Int.natCast_dvd_natCast.2 hmq)))
  rw [ramanujanSum_prime_pow_succ hp]
  split_ifs with h1 h2 h2
  · have hpow : (p : ℝ) ^ k ≤ (p : ℝ) ^ (k + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le) k.le_succ
    have hreal :
        (p : ℂ) ^ (k + 1) - (p : ℂ) ^ k = (((p : ℝ) ^ (k + 1) - (p : ℝ) ^ k : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hreal, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 hpow)]
    exact (sub_le_self _ (by positivity)).trans (by simpa using hle (by exact_mod_cast h1) dvd_rfl)
  · simpa using hle (by exact_mod_cast h1) dvd_rfl
  · simpa using hle (by exact_mod_cast h2) (pow_dvd_pow _ k.le_succ)
  · simp

/-- `|c_q(n)| ≤ gcd(n, q)`. -/
theorem norm_ramanujanSum_le (q : ℕ) (n : ℤ) : ‖ramanujanSum q n‖ ≤ Int.gcd n q := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hp => exact norm_ramanujanSum_prime_pow_le hp k n
  | coprime a b _ _ hab ha hb =>
    have hgcd : Int.gcd n (a * b : ℕ) = Int.gcd n a * Int.gcd n b := by
      simpa only [Int.gcd_def, Int.natAbs_natCast] using Nat.Coprime.gcd_mul _ hab
    rw [ramanujanSum_mul hab, norm_mul, hgcd, Nat.cast_mul]
    exact mul_le_mul ha hb (norm_nonneg _) (Nat.cast_nonneg _)

/-! ### Examples -/

example : ramanujanSum 2 1 = -1 := by
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

example : ramanujanSum 6 0 = 2 := by
  rw [ramanujanSum_zero_right, show Nat.totient 6 = 2 by decide]
  norm_num

example : ramanujanSum 4 2 = -2 := by
  rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num, ramanujanSum_prime_pow_succ Nat.prime_two]
  norm_num

example : ramanujanSum 12 6 = -4 := by
  rw [show (12 : ℕ) = 2 ^ (1 + 1) * 3 by norm_num, ramanujanSum_mul (by decide),
    ramanujanSum_prime_pow_succ Nat.prime_two, ramanujanSum_prime Nat.prime_three]
  norm_num

end TauCeti
