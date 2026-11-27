/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import TauCeti.NumberTheory.SelbergSieve.Legendre

/-!
# Prime-factor density bounds and strict-cutoff remainder mass for `BoundingSieve`

At every prime factor `p ∈ s.prodPrimes.primeFactors` of a `BoundingSieve`, both the local density
`s.nu p` and its complementary Euler factor `1 - s.nu p` are strictly positive.

`BoundingSieve.remainderMass s D` sums `|s.rem d|` over positive divisors `d ∣ s.prodPrimes`
strictly below a real cutoff `D` (including `d = 1` when `1 < D`) and bounds `s.errSum w` whenever
`w` is bounded on `s.prodPrimes.divisors` and supported strictly below `D`.

## Main definitions and results

* `BoundingSieve.nu_pos_of_mem_primeFactors`, `BoundingSieve.one_sub_nu_pos_of_mem_primeFactors`:
  positivity of `s.nu p` and `1 - s.nu p` at prime factors `p ∈ s.prodPrimes.primeFactors`.
* `BoundingSieve.remainderMass`: truncated absolute remainder sum on `(d : ℝ) < D`, together with
  `remainderMass_def`, `remainderMass_nonneg`, `remainderMass_mono`,
  `remainderMass_eq_zero_of_le_one`, `remainderMass_congr`, and `errSum_le_mul_remainderMass`.

## References

* K. S. Kedlaya, *Notes on Analytic Number Theory*, Chapter 12, §12.2.
* D. R. Heath-Brown, *Lectures on sieves*, §1 (2002).
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
@[simp]
theorem remainderMass_eq_zero_of_le_one (s : BoundingSieve) {D : ℝ} (hD : D ≤ 1) :
    s.remainderMass D = 0 := by
  rw [remainderMass, sum_eq_zero]
  intro d hd
  rw [mem_filter] at hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd.1
  linarith

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
  rcases le_or_gt D 1 with hD1 | hD1
  · rw [s.remainderMass_eq_zero_of_le_one hD1, mul_zero, errSum, sum_eq_zero]
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    rw [hsupp d hd (hD1.trans hd1), abs_zero, zero_mul]
  · have hceil : 1 ≤ ⌈D⌉₊ :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (zero_lt_one.trans hD1)).ne'
    have hlt_iff (d : ℕ) : d ≤ ⌈D⌉₊ - 1 ↔ (d : ℝ) < D := by
      rw [← Nat.lt_ceil]; omega
    have hfilter : {d ∈ s.prodPrimes.divisors | d ≤ ⌈D⌉₊ - 1} =
        s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < D) := by
      ext d; simp only [mem_filter, hlt_iff]
    rw [remainderMass, ← hfilter]
    exact s.errSum_le_mul_sum_abs_rem
      (fun d hd hgt ↦ hsupp d (mem_divisors.mpr ⟨hd, s.prodPrimes_ne_zero⟩)
        (le_of_not_gt (mt (hlt_iff d).mpr hgt.not_ge)))
      (fun d hd _ ↦ hw d (mem_divisors.mpr ⟨hd, s.prodPrimes_ne_zero⟩))

end BoundingSieve
