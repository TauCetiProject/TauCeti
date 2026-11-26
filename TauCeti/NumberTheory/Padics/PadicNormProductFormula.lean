/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The product formula for a rational number over the primes below a bound

For a nonzero rational number `q` and a bound `B` larger than the numerator and the denominator
of `|q|`, every prime `p` with `|q|_p ≠ 1` is below `B`, so the product formula for `q` is a
finite product over the primes `p < B`. For `q = 0` every `|q|_p` is `0`; the logarithmic form
still holds, since both of its terms vanish by the convention `Real.log 0 = 0`.

## Main results

* `padicNorm.eq_div_of_ne_zero`: `|q|_p = p ^ v_p(den q) / p ^ v_p(num q)` for `q ≠ 0`, with
  `v_p` the multiplicity.
* `Rat.abs_mul_prod_padicNorm_eq_one`: `|q| · ∏_{p < B prime} |q|_p = 1` for `q ≠ 0`.
* `Rat.log_abs_add_sum_log_padicNorm_eq_zero`: `log |q| + ∑_{p < B prime} log |q|_p = 0`, also
  for `q = 0` with Mathlib's convention `Real.log 0 = 0`.

## References

* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.log_product_formula`).
-/

public section

open Finset

/-- The `p`-adic norm of a nonzero rational number `q` through the multiplicities of `p` in its
numerator and its denominator: `|q|_p = p ^ v_p(q.den) / p ^ v_p(|q.num|)`. No primality of `p`
is needed: for `p = 0` and `p = 1` both sides are `1`. -/
theorem padicNorm.eq_div_of_ne_zero {q : ℚ} (hq : q ≠ 0) (p : ℕ) :
    padicNorm p q = (p : ℚ) ^ multiplicity p q.den / (p : ℚ) ^ multiplicity p q.num.natAbs := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [padicNorm, hq, padicValRat_def, padicValInt]
  rw [padicNorm.eq_zpow_of_ne_zero hq, padicValRat_def, padicValInt, neg_sub,
    zpow_sub₀ (by exact_mod_cast hp), zpow_natCast, zpow_natCast]

namespace Rat

/-- **Product formula** for a nonzero rational number, over the primes below a bound `B` larger
than its numerator and its denominator: `|q| · ∏_{p < B prime} |q|_p = 1`. -/
theorem abs_mul_prod_padicNorm_eq_one {q : ℚ} (hq : q ≠ 0) {B : ℕ} (hnum : q.num.natAbs < B)
    (hden : q.den < B) : |q| * ∏ p ∈ range B with p.Prime, padicNorm p q = 1 := by
  rw [prod_congr rfl fun p _ ↦ by rw [padicNorm.eq_div_of_ne_zero hq p, ← Nat.cast_pow,
      ← Nat.cast_pow], prod_div_distrib,
    ← Nat.cast_prod, ← Nat.cast_prod, Nat.prod_pow_prime_multiplicity _ q.den_ne_zero _ hden,
    Nat.prod_pow_prime_multiplicity _ (by simpa using hq) _ hnum]
  nth_rw 1 [← q.num_div_den]
  have h1 : (q.num.natAbs : ℚ) ≠ 0 := by simpa using hq
  rw [abs_div, Nat.abs_cast, Nat.cast_natAbs, Int.cast_abs]
  field_simp [h1]

/-- **Product formula** in logarithmic form, over the primes below a bound `B` larger than the
numerator and the denominator of `q`: `log |q| + ∑_{p < B prime} log |q|_p = 0`. For `q = 0`
both sides vanish by the convention `Real.log 0 = 0`. -/
theorem log_abs_add_sum_log_padicNorm_eq_zero (q : ℚ) {B : ℕ} (hnum : q.num.natAbs < B)
    (hden : q.den < B) :
    Real.log |(q : ℝ)| + ∑ p ∈ range B with p.Prime, Real.log (padicNorm p q) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hprod := congrArg (fun x : ℚ ↦ Real.log x) (abs_mul_prod_padicNorm_eq_one hq hnum hden)
  have hne : ∀ p ∈ {p ∈ range B | p.Prime}, ((padicNorm p q : ℚ) : ℝ) ≠ 0 := fun p hp ↦ by
    have := Fact.mk (mem_filter.1 hp).2
    exact_mod_cast padicNorm.ne_zero hq
  simp only [cast_mul, cast_abs, cast_prod, cast_one, Real.log_one] at hprod
  rwa [Real.log_mul (by simpa using hq) (prod_ne_zero_iff.2 hne), Real.log_prod hne] at hprod

end Rat
