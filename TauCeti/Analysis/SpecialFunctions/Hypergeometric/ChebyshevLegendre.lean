/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import TauCeti.Algebra.Polynomial.HasseDeriv
import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Chebyshev and Legendre polynomials as terminating `₂F₁`

For `n : ℕ` and every `x : ℂ` (DLMF 15.9.5–15.9.7):

* `Tₙ(x) = ₂F₁(−n, n; ½; (1 − x)/2)`;
* `Uₙ(x) = (n + 1) ₂F₁(−n, n + 2; 3/2; (1 − x)/2)`;
* `P*ₙ(y) = ₂F₁(−n, n + 1; 1; y)` for Mathlib's shifted Legendre polynomial `P*ₙ`, so that
  `Pₙ(x) = P*ₙ((1 − x)/2) = ₂F₁(−n, n + 1; 1; (1 − x)/2)`.

Here `T` and `U` are Mathlib's `Polynomial.Chebyshev.T` and `Polynomial.Chebyshev.U`, and `₂F₁`
is Mathlib's `ordinaryHypergeometric`.

## Main results

* `TauCeti.chebyshevT_eq_ordinaryHypergeometric` (DLMF 15.9.5).
* `TauCeti.chebyshevU_eq_ordinaryHypergeometric` (DLMF 15.9.6).
* `TauCeti.shiftedLegendre_eval_eq_ordinaryHypergeometric` (DLMF 15.9.7).

## Implementation notes

Both sides are polynomials of degree at most `n` in `x`, compared coefficient by coefficient.
For `T` and `U` the coefficients are those of the Taylor expansion at `x = 1`, which Mathlib's
`Polynomial.Chebyshev.iterate_derivative_T_eval_one_eq_div` and
`Polynomial.Chebyshev.iterate_derivative_U_eval_one_eq_div` compute. For the shifted Legendre
polynomial they are given by `Polynomial.coeff_shiftedLegendre`. The Taylor formula is
`Polynomial.eval_eq_sum_range_iterate_derivative_eval`, and the terminating series is
`TauCeti.ordinaryHypergeometric_neg_nat_eq_sum`.
-/

public section

open Polynomial Finset

open scoped Nat

namespace TauCeti

/-- A terminating `₂F₁(−n, a; b/2; (1 − x)/2)` as a polynomial in `x − 1`: if
`(−n)ₖ (a)ₖ = (−1)ᵏ Dₖ` for every `k`, then
`₂F₁(−n, a; b/2; (1 − x)/2) = ∑_{k ≤ n} Dₖ / ∏_{l<k} (2l + b) / k! (x − 1)ᵏ`. Where some `2l + b`
vanishes, both sides of the `k`-th term take the junk value `0`. This is the common form of
15.9.5 and 15.9.6. -/
private theorem ordinaryHypergeometric_neg_nat_div_two_eq_sum (n : ℕ) (a b x : ℂ) {D : ℕ → ℂ}
    (hD : ∀ k, (ascPochhammer ℂ k).eval (-n : ℂ) * (ascPochhammer ℂ k).eval a = (-1) ^ k * D k) :
    ₂F₁ (-n : ℂ) a (b / 2) ((1 - x) / 2) =
      ∑ k ∈ range (n + 1), D k / (∏ l ∈ range k, (2 * (l : ℂ) + b)) / k ! * (x - 1) ^ k := by
  rw [ordinaryHypergeometric_neg_nat_eq_sum]
  refine sum_congr rfl fun k _ => ?_
  have hkf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  -- `(b/2)ₖ = ∏_{l<k} (2l + b) / 2ᵏ` and `((1 − x)/2)ᵏ = (−1)ᵏ (x − 1)ᵏ / 2ᵏ`; the two powers of
  -- `2` cancel, and so do the two signs `(−1)ᵏ`.
  have hP : (ascPochhammer ℂ k).eval (b / 2) = (∏ l ∈ range k, (2 * (l : ℂ) + b)) / 2 ^ k := by
    rw [eq_div_iff (pow_ne_zero _ two_ne_zero), mul_comm, two_pow_mul_ascPochhammer_eval_div_two]
  have hx : ((1 - x) / 2) ^ k = (-1) ^ k * (x - 1) ^ k / 2 ^ k := by
    rw [div_pow, ← mul_pow, neg_one_mul, neg_sub]
  have hsign : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [smul_eq_mul, mul_assoc ((k ! : ℂ)⁻¹), hD, hP, hx]
  by_cases hQ : ∏ l ∈ range k, (2 * (l : ℂ) + b) = 0
  · simp [hQ]
  calc _ = ((-1 : ℂ) ^ k * (-1) ^ k) *
        (D k / (∏ l ∈ range k, (2 * (l : ℂ) + b)) / k ! * (x - 1) ^ k) := by
          field_simp
      _ = _ := by rw [hsign, one_mul]

/-- **DLMF 15.9.5.** `Tₙ(x) = ₂F₁(−n, n; ½; (1 − x)/2)` for `n : ℕ` and every `x : ℂ`. -/
theorem chebyshevT_eq_ordinaryHypergeometric (n : ℕ) (x : ℂ) :
    (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval x = ₂F₁ (-n : ℂ) n (1 / 2) ((1 - x) / 2) := by
  rw [ordinaryHypergeometric_neg_nat_div_two_eq_sum n n 1 x
      (ascPochhammer_eval_neg_mul_ascPochhammer_eval (n : ℂ)),
    eval_eq_sum_range_iterate_derivative_eval (N := n + 1)
      (by rw [Polynomial.Chebyshev.natDegree_T]; simp) 1 x]
  refine sum_congr rfl fun k _ => ?_
  rw [Polynomial.Chebyshev.iterate_derivative_T_eval_one_eq_div]
  push_cast
  ring

/-- **DLMF 15.9.6.** `Uₙ(x) = (n + 1) ₂F₁(−n, n + 2; 3/2; (1 − x)/2)` for `n : ℕ` and every
`x : ℂ`. -/
theorem chebyshevU_eq_ordinaryHypergeometric (n : ℕ) (x : ℂ) :
    (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval x =
      (n + 1) * ₂F₁ (-n : ℂ) (n + 2) (3 / 2) ((1 - x) / 2) := by
  rw [ordinaryHypergeometric_neg_nat_div_two_eq_sum n (n + 2) 3 x
      (ascPochhammer_eval_neg_mul_ascPochhammer_eval_add_two (n : ℂ)),
    eval_eq_sum_range_iterate_derivative_eval (N := n + 1)
      (by rw [Polynomial.Chebyshev.natDegree_U]; omega) 1 x, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Polynomial.Chebyshev.iterate_derivative_U_eval_one_eq_div]
  push_cast
  ring

/-- **DLMF 15.9.7.** Mathlib's shifted Legendre polynomial is the terminating Gauss series,
`P*ₙ(y) = ₂F₁(−n, n + 1; 1; y)` for `n : ℕ` and every `y : ℂ`, with no further sign. At
`y = (1 − x)/2` both sides are the Legendre polynomial `Pₙ(x)`. -/
theorem shiftedLegendre_eval_eq_ordinaryHypergeometric (n : ℕ) (y : ℂ) :
    ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℂ)).eval y =
      ₂F₁ (-n : ℂ) (n + 1) 1 y := by
  rw [ordinaryHypergeometric_neg_nat_eq_sum, eval_eq_sum_range'
    (Nat.lt_succ_of_le ((natDegree_map_le).trans (natDegree_shiftedLegendre n).le))]
  refine sum_congr rfl fun k _ => ?_
  -- `(n + 1)ₖ = k! C(n + k, k)`, computed in `ℕ` as a rising factorial.
  have hpos : (ascPochhammer ℂ k).eval ((n : ℂ) + 1) = k ! * (n + k).choose k := by
    have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, ← ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hkf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [coeff_map, coeff_shiftedLegendre, ascPochhammer_eval_neg_natCast, hpos,
    ascPochhammer_eval_one, Nat.choose_symm_add, eq_intCast, smul_eq_mul]
  push_cast
  field_simp

end TauCeti
