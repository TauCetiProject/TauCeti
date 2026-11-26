/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve

/-!
# Local upper-Möbius brackets and strict-cutoff remainder mass for `BoundingSieve`

Extending a sieve weight sequence by `0` outside divisors of `s.prodPrimes` turns pointwise
upper-Möbius bounds local to divisors `r ∣ s.prodPrimes` into Mathlib's global
`BoundingSieve.IsUpperMoebius`, giving the upper counterparts of the local lower-Möbius brackets in
`TauCeti.NumberTheory.SelbergSieve.Legendre`.

`BoundingSieve.remainderMass s D` sums `|s.rem d|` over positive divisors `d ∣ s.prodPrimes`
strictly below a real cutoff `D` (including `d = 1` when `1 < D`) and bounds `s.errSum w` whenever
`w` is bounded on `s.prodPrimes.divisors` and supported strictly below `D`.

## Main definitions and results

* `BoundingSieve.nu_pos_of_mem_primeFactors`, `BoundingSieve.one_sub_nu_pos_of_mem_primeFactors`:
  positivity of `s.nu p` and `1 - s.nu p` at prime factors `p ∈ s.prodPrimes.primeFactors`.
* `BoundingSieve.isUpperMoebius_ite_dvd`,
  `BoundingSieve.siftedSum_le_sum_mul_multSum`,
  `BoundingSieve.siftedSum_le_totalMass_mul_mainSum_add_errSum`: upper sieve brackets from
  divisor-sum bounds local to divisors of `s.prodPrimes`, refining
  `BoundingSieve.siftedSum_le_sum_of_upperMoebius` and
  `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`.
* `BoundingSieve.remainderMass`: truncated absolute remainder sum on `(d : ℝ) < D`, together with
  its monotonicity, vanishing below `1`, congruence, and `errSum` comparison lemmas.

## References

* D. R. Heath-Brown, *Lectures on sieves*, §1 (2002).
* K. S. Kedlaya, *Notes on Analytic Number Theory*, Chapter 12.
-/

public noncomputable section

open Finset Nat

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

/-- Extending `muPlus` by `0` outside divisors of `s.prodPrimes` turns upper-Möbius bounds local to
divisors `r ∣ s.prodPrimes` into a global `BoundingSieve.IsUpperMoebius` sequence. -/
theorem isUpperMoebius_ite_dvd (s : BoundingSieve) {muPlus : ℕ → ℝ}
    (h : ∀ r, r ∣ s.prodPrimes → (if r = 1 then 1 else 0) ≤ ∑ d ∈ r.divisors, muPlus d) :
    IsUpperMoebius (fun d ↦ if d ∣ s.prodPrimes then muPlus d else 0) := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hdiv : {d ∈ n.divisors | d ∣ s.prodPrimes} = (Nat.gcd s.prodPrimes n).divisors := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hn, Nat.gcd_ne_zero_left s.prodPrimes_ne_zero,
      and_comm]
  rw [← sum_filter, hdiv]
  refine le_trans ?_ (h (Nat.gcd s.prodPrimes n) (Nat.gcd_dvd_left _ _))
  split_ifs with hn1 hgcd <;> simp_all

/-- Upper sieve coefficients local to divisors `r ∣ s.prodPrimes` bound `s.siftedSum` above in
terms of `s.multSum`, refining `BoundingSieve.siftedSum_le_sum_of_upperMoebius` and matching
`BoundingSieve.sum_mul_multSum_le_siftedSum`. -/
theorem siftedSum_le_sum_mul_multSum (s : BoundingSieve) {c : ℕ → ℝ}
    (hc : ∀ r, r ∣ s.prodPrimes → (if r = 1 then 1 else 0) ≤ ∑ d ∈ r.divisors, c d) :
    s.siftedSum ≤ ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d := by
  let w : ℕ → ℝ := fun d ↦ if d ∣ s.prodPrimes then c d else 0
  have hsum : ∑ d ∈ s.prodPrimes.divisors, w d * s.multSum d =
      ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d :=
    sum_congr rfl fun d hd ↦ by simp [w, Nat.dvd_of_mem_divisors hd]
  simpa only [hsum] using s.siftedSum_le_sum_of_upperMoebius w (s.isUpperMoebius_ite_dvd hc)

/-- Upper sieve coefficients local to divisors `r ∣ s.prodPrimes` yield
`s.siftedSum ≤ s.totalMass * s.mainSum c + s.errSum c`, refining
`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius` and matching
`BoundingSieve.totalMass_mul_mainSum_sub_errSum_le_siftedSum`. -/
theorem siftedSum_le_totalMass_mul_mainSum_add_errSum (s : BoundingSieve) {c : ℕ → ℝ}
    (hc : ∀ r, r ∣ s.prodPrimes → (if r = 1 then 1 else 0) ≤ ∑ d ∈ r.divisors, c d) :
    s.siftedSum ≤ s.totalMass * s.mainSum c + s.errSum c := by
  let w : ℕ → ℝ := fun d ↦ if d ∣ s.prodPrimes then c d else 0
  have hmain : s.mainSum w = s.mainSum c :=
    sum_congr rfl fun d hd ↦ by simp [w, Nat.dvd_of_mem_divisors hd]
  have herr : s.errSum w = s.errSum c :=
    sum_congr rfl fun d hd ↦ by simp [w, Nat.dvd_of_mem_divisors hd]
  simpa only [hmain, herr] using
    s.siftedSum_le_mainSum_errSum_of_upperMoebius w (s.isUpperMoebius_ite_dvd hc)

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
