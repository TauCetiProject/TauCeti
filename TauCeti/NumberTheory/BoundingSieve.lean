/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve

/-!
# Exact Legendre identities, divisor-sum brackets, and remainder mass for `BoundingSieve`

For a `BoundingSieve`, interchanging summation over divisors of `s.prodPrimes` with summation over
`s.support` expresses any weighted multiple sum `∑ d ∣ P, c d * s.multSum d` in terms of the inner
divisor sums `∑ d ∣ gcd(P, n), c d`. Specializing `c` to the Möbius function gives the exact
Legendre identity and its Euler-product decomposition, while pointwise lower or upper bounds on
`∑ d ∣ r, c d` restricted to divisors `r ∣ s.prodPrimes` give lower and upper brackets on
`s.siftedSum` in terms of `s.mainSum` and `s.errSum` without any global hypothesis outside the
divisors of `s.prodPrimes`.

`BoundingSieve.remainderMass s D` sums `|s.rem d|` over positive divisors `d ∣ s.prodPrimes`
strictly below a real cutoff `D` (including `d = 1` when `1 < D`) and bounds `s.errSum w` whenever
`w` is bounded on `s.prodPrimes.divisors` and supported strictly below `D`.

## Main definitions and results

* `BoundingSieve.nu_pos_of_mem_primeFactors`, `BoundingSieve.one_sub_nu_pos_of_mem_primeFactors`:
  positivity of `s.nu p` and `1 - s.nu p` at prime factors `p ∈ s.prodPrimes.primeFactors`.
* `BoundingSieve.sum_divisors_mul_multSum`: weighted divisibility interchange over `s.support`.
* `BoundingSieve.mainSum_moebius`, `BoundingSieve.siftedSum_eq_sum_divisors_moebius_mul_multSum`,
  `BoundingSieve.siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem`: the Legendre identity
  and its Euler-product main term.
* `BoundingSieve.totalMass_mul_mainSum_sub_errSum_le_siftedSum_of_dvd`,
  `BoundingSieve.siftedSum_le_totalMass_mul_mainSum_add_errSum_of_dvd`: lower and upper sieve
  brackets from divisor-sum bounds on divisors of `s.prodPrimes`.
* `BoundingSieve.remainderMass`: truncated absolute remainder sum on `(d : ℝ) < D`, together with
  its monotonicity, vanishing below `1`, congruence, and `errSum` comparison lemmas.

## References

* D. R. Heath-Brown, *Lectures on sieves*, §1 (2002).
* K. S. Kedlaya, *Notes on Analytic Number Theory*, Chapter 12.
-/

public noncomputable section

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace BoundingSieve

/-- At every prime factor `p` of `s.prodPrimes`, the local density `s.nu p` is positive. -/
theorem nu_pos_of_mem_primeFactors (s : BoundingSieve) {p : ℕ}
    (hp : p ∈ s.prodPrimes.primeFactors) : 0 < s.nu p :=
  s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- At every prime factor `p` of `s.prodPrimes`, the Euler factor `1 - s.nu p` is positive. -/
theorem one_sub_nu_pos_of_mem_primeFactors (s : BoundingSieve) {p : ℕ}
    (hp : p ∈ s.prodPrimes.primeFactors) : 0 < 1 - s.nu p :=
  sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp))

/-- Weighted divisibility interchange: summing `c d * s.multSum d` over `d ∣ s.prodPrimes` equals
summing `s.weights n` times the divisor sum of `c` over `Nat.gcd s.prodPrimes n`. -/
theorem sum_divisors_mul_multSum (s : BoundingSieve) (c : ℕ → ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d =
      ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, c d := by
  have hgcd (n : ℕ) : (Nat.gcd s.prodPrimes n).divisors =
      s.prodPrimes.divisors.filter (· ∣ n) := by
    rw [← Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
    ext d
    simp +contextual [Nat.dvd_gcd_iff]
  calc ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d
      = ∑ d ∈ s.prodPrimes.divisors, ∑ n ∈ s.support,
          if d ∣ n then s.weights n * c d else 0 := by
        refine sum_congr rfl fun d _ ↦ ?_
        simp_rw [multSum, mul_sum, mul_ite, mul_zero, mul_comm (c d)]
    _ = ∑ n ∈ s.support, ∑ d ∈ s.prodPrimes.divisors,
          if d ∣ n then s.weights n * c d else 0 := sum_comm
    _ = ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, c d := by
        refine sum_congr rfl fun n _ ↦ ?_
        rw [hgcd n, mul_sum, sum_filter]

/-- Decomposing `s.multSum d = s.nu d * s.totalMass + s.rem d` splits a weighted multiple sum into
`s.totalMass * s.mainSum c` plus the weighted remainder sum. -/
theorem sum_divisors_mul_multSum_eq_totalMass_mul_mainSum_add (s : BoundingSieve) (c : ℕ → ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d =
      s.totalMass * s.mainSum c + ∑ d ∈ s.prodPrimes.divisors, c d * s.rem d := by
  rw [mainSum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [s.multSum_eq_main_err d]
  ring

/-- The Möbius main sum over `s.prodPrimes.divisors` equals the Euler product
`∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)`. -/
theorem mainSum_moebius (s : BoundingSieve) :
    s.mainSum (fun d ↦ (μ d : ℝ)) = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  simpa only [mainSum, intCoe_apply] using
    (s.nu_mult.prodPrimeFactors_one_sub s.nu s.prodPrimes_ne_zero).symm

/-- **Legendre's sieve identity**: `s.siftedSum` is the Möbius-weighted sum of `s.multSum` over
divisors of `s.prodPrimes`. -/
theorem siftedSum_eq_sum_divisors_moebius_mul_multSum (s : BoundingSieve) :
    s.siftedSum = ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.multSum d := by
  rw [sum_divisors_mul_multSum, s.siftedSum_eq_sum_support_mul_ite]
  refine sum_congr rfl fun n _ ↦ congrArg (s.weights n * ·) ?_
  have h1 := congrArg (fun f : ArithmeticFunction ℝ ↦ f (Nat.gcd s.prodPrimes n))
    (coe_moebius_mul_coe_zeta (R := ℝ))
  rw [coe_mul_zeta_apply] at h1
  split_ifs with hgcd
  · simp [hgcd]
  · simpa [ArithmeticFunction.one_apply_ne hgcd] using h1.symm

/-- **Legendre's identity with main term and remainder**: `s.siftedSum` equals `s.totalMass` times
the Euler product plus the Möbius-weighted remainder sum. -/
theorem siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem (s : BoundingSieve) :
    s.siftedSum = s.totalMass * (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) +
      ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.rem d := by
  rw [s.siftedSum_eq_sum_divisors_moebius_mul_multSum,
    s.sum_divisors_mul_multSum_eq_totalMass_mul_mainSum_add, s.mainSum_moebius]

/-- The error in Legendre's approximation to `s.siftedSum` is bounded by the full absolute
remainder sum over `s.prodPrimes.divisors`. -/
theorem abs_siftedSum_sub_totalMass_mul_prod_le (s : BoundingSieve) :
    |s.siftedSum - s.totalMass * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
      ∑ d ∈ s.prodPrimes.divisors, |s.rem d| := by
  rw [s.siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ ↦ ?_)
  rw [abs_mul]
  have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
  exact mul_le_of_le_one_left (abs_nonneg _) hμ

/-- Pointwise lower-Möbius bounds on divisors `r ∣ s.prodPrimes` yield a lower bound on
`s.siftedSum` in terms of `s.multSum`. -/
theorem sum_le_siftedSum_of_dvd (s : BoundingSieve) (muMinus : ℕ → ℝ)
    (h : ∀ r, r ∣ s.prodPrimes → ∑ d ∈ r.divisors, muMinus d ≤ if r = 1 then 1 else 0) :
    ∑ d ∈ s.prodPrimes.divisors, muMinus d * s.multSum d ≤ s.siftedSum := by
  rw [sum_divisors_mul_multSum, s.siftedSum_eq_sum_support_mul_ite]
  gcongr with n
  exact h (Nat.gcd s.prodPrimes n) (Nat.gcd_dvd_left _ _)

/-- Pointwise upper-Möbius bounds on divisors `r ∣ s.prodPrimes` yield an upper bound on
`s.siftedSum` in terms of `s.multSum`. -/
theorem siftedSum_le_sum_of_dvd (s : BoundingSieve) (muPlus : ℕ → ℝ)
    (h : ∀ r, r ∣ s.prodPrimes → (if r = 1 then 1 else 0) ≤ ∑ d ∈ r.divisors, muPlus d) :
    s.siftedSum ≤ ∑ d ∈ s.prodPrimes.divisors, muPlus d * s.multSum d := by
  rw [sum_divisors_mul_multSum, s.siftedSum_eq_sum_support_mul_ite]
  gcongr with n
  exact h (Nat.gcd s.prodPrimes n) (Nat.gcd_dvd_left _ _)

/-- Pointwise lower-Möbius bounds on divisors `r ∣ s.prodPrimes` yield
`s.totalMass * s.mainSum muMinus - s.errSum muMinus ≤ s.siftedSum`, with no sign assumption on
`s.totalMass`. -/
theorem totalMass_mul_mainSum_sub_errSum_le_siftedSum_of_dvd (s : BoundingSieve) (muMinus : ℕ → ℝ)
    (h : ∀ r, r ∣ s.prodPrimes → ∑ d ∈ r.divisors, muMinus d ≤ if r = 1 then 1 else 0) :
    s.totalMass * s.mainSum muMinus - s.errSum muMinus ≤ s.siftedSum := by
  refine le_trans ?_ (s.sum_le_siftedSum_of_dvd muMinus h)
  rw [s.sum_divisors_mul_multSum_eq_totalMass_mul_mainSum_add, sub_eq_add_neg, errSum,
    ← sum_neg_distrib]
  gcongr _ + ∑ d ∈ _, ?_ with d
  rw [← abs_mul]
  exact neg_abs_le _

/-- Pointwise upper-Möbius bounds on divisors `r ∣ s.prodPrimes` yield
`s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus`, refining
`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius` to hypotheses local to divisors of
`s.prodPrimes`. -/
theorem siftedSum_le_totalMass_mul_mainSum_add_errSum_of_dvd (s : BoundingSieve) (muPlus : ℕ → ℝ)
    (h : ∀ r, r ∣ s.prodPrimes → (if r = 1 then 1 else 0) ≤ ∑ d ∈ r.divisors, muPlus d) :
    s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus := by
  refine (s.siftedSum_le_sum_of_dvd muPlus h).trans ?_
  rw [s.sum_divisors_mul_multSum_eq_totalMass_mul_mainSum_add, errSum]
  gcongr _ + ∑ d ∈ _, ?_ with d
  rw [← abs_mul]
  exact le_abs_self _

/-- Sum of `|s.rem d|` over positive divisors `d ∣ s.prodPrimes` strictly below `D`, including
`d = 1` whenever `1 < D`. -/
def remainderMass (s : BoundingSieve) (D : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < D), |s.rem d|

/-- Explicit sum formula for `BoundingSieve.remainderMass`. -/
theorem remainderMass_def (s : BoundingSieve) (D : ℝ) :
    s.remainderMass D =
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < D), |s.rem d| := (rfl)

/-- `s.remainderMass D` is nonnegative at every real cutoff `D`. -/
theorem remainderMass_nonneg (s : BoundingSieve) (D : ℝ) : 0 ≤ s.remainderMass D :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-- `s.remainderMass` is monotone in the real cutoff `D`. -/
theorem remainderMass_mono (s : BoundingSieve) {D₁ D₂ : ℝ} (h : D₁ ≤ D₂) :
    s.remainderMass D₁ ≤ s.remainderMass D₂ := by
  refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ abs_nonneg _
  intro d hd
  rw [mem_filter] at hd ⊢
  exact ⟨hd.1, hd.2.trans_le h⟩

/-- Every positive divisor satisfies `1 ≤ d`, so `s.remainderMass D = 0` when `D ≤ 1`. -/
theorem remainderMass_eq_zero_of_le_one (s : BoundingSieve) {D : ℝ} (hD : D ≤ 1) :
    s.remainderMass D = 0 := by
  rw [remainderMass, sum_eq_zero]
  intro d hd
  rw [mem_filter] at hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd.1
  linarith

/-- At cutoff `1`, `s.remainderMass 1 = 0`. -/
@[simp]
theorem remainderMass_one (s : BoundingSieve) : s.remainderMass 1 = 0 :=
  s.remainderMass_eq_zero_of_le_one le_rfl

/-- At cutoff `0`, `s.remainderMass 0 = 0`. -/
@[simp]
theorem remainderMass_zero (s : BoundingSieve) : s.remainderMass 0 = 0 :=
  s.remainderMass_eq_zero_of_le_one zero_le_one

/-- `remainderMass` depends only on `prodPrimes` and on `|rem d|` for divisors `d` below `D`. -/
theorem remainderMass_congr {s₁ s₂ : BoundingSieve} {D : ℝ}
    (hP : s₁.prodPrimes = s₂.prodPrimes)
    (hrem : ∀ d ∈ s₁.prodPrimes.divisors, (d : ℝ) < D → |s₁.rem d| = |s₂.rem d|) :
    s₁.remainderMass D = s₂.remainderMass D := by
  rw [remainderMass, remainderMass, ← hP]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [mem_filter] at hd
  exact hrem d hd.1 hd.2

/-- If `|w d| ≤ M` on `s.prodPrimes.divisors` and `w` vanishes for `D ≤ d`, then
`s.errSum w ≤ M * s.remainderMass D`. -/
theorem errSum_le_mul_remainderMass (s : BoundingSieve) (w : ℕ → ℝ) (D M : ℝ)
    (hw : ∀ d ∈ s.prodPrimes.divisors, |w d| ≤ M)
    (hsupp : ∀ d ∈ s.prodPrimes.divisors, D ≤ (d : ℝ) → w d = 0) :
    s.errSum w ≤ M * s.remainderMass D := by
  rw [errSum, remainderMass, mul_sum, sum_filter]
  refine sum_le_sum fun d hd ↦ ?_
  split_ifs with hlt
  · exact mul_le_mul_of_nonneg_right (hw d hd) (abs_nonneg _)
  · rw [hsupp d hd (le_of_not_gt hlt), abs_zero, zero_mul]

/-- Unit-modulus weights supported strictly below `D` have `s.errSum w ≤ s.remainderMass D`. -/
theorem errSum_le_remainderMass (s : BoundingSieve) (w : ℕ → ℝ) (D : ℝ)
    (hw : ∀ d ∈ s.prodPrimes.divisors, |w d| ≤ 1)
    (hsupp : ∀ d ∈ s.prodPrimes.divisors, D ≤ (d : ℝ) → w d = 0) :
    s.errSum w ≤ s.remainderMass D := by
  simpa only [one_mul] using s.errSum_le_mul_remainderMass w D 1 hw hsupp

end BoundingSieve
