/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
# Chebyshev and Legendre polynomials as terminating `₂F₁`

For `n : ℕ` and every `x : ℂ` (DLMF 15.9.5–15.9.7):

* `Tₙ(x) = ₂F₁(−n, n; ½; (1 − x)/2)`;
* `Uₙ(x) = (n + 1) ₂F₁(−n, n + 2; 3/2; (1 − x)/2)`;
* `P̃ₙ(y) = ₂F₁(−n, n + 1; 1; y)` for Mathlib's shifted Legendre polynomial `P̃ₙ`, so that
  `Pₙ(x) = P̃ₙ((1 − x)/2) = ₂F₁(−n, n + 1; 1; (1 − x)/2)`.

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
polynomial they are given by `Polynomial.coeff_shiftedLegendre`.
-/

@[expose] public section

open Polynomial Finset

open scoped Nat

namespace TauCeti

/-- A terminating `₂F₁(−n, b; c; z)` is the sum of its first `n + 1` terms. -/
private theorem ordinaryHypergeometric_neg_nat_eq_sum (n : ℕ) (b c z : ℂ) :
    ordinaryHypergeometric (-n : ℂ) b c z =
      ∑ k ∈ range (n + 1), ((k ! : ℂ)⁻¹ * (ascPochhammer ℂ k).eval (-n : ℂ) *
        (ascPochhammer ℂ k).eval b * ((ascPochhammer ℂ k).eval c)⁻¹) * z ^ k := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  refine tsum_eq_sum fun k hk => ?_
  rw [ascPochhammer_eval_neg_natCast_of_lt (by simpa using hk)]
  simp

/-- The Taylor expansion of a complex polynomial at `1`. -/
private theorem eval_eq_sum_iterate_derivative_eval_one (p : ℂ[X]) {N : ℕ}
    (hN : p.natDegree < N) (x : ℂ) :
    p.eval x = ∑ k ∈ range N, (derivative^[k] p).eval 1 / k ! * (x - 1) ^ k := by
  have h := taylor_eval (1 : ℂ) p (x - 1)
  rw [sub_add_cancel] at h
  rw [← h, eval_eq_sum_range' (by rwa [natDegree_taylor]) (x - 1)]
  refine sum_congr rfl fun k _ => ?_
  have hk : (derivative^[k] p).eval 1 = k ! * (hasseDeriv k p).eval 1 := by
    rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul, eval_mul, eval_natCast]
  have hkf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [taylor_coeff, hk]
  field_simp

/-- `(−a)ₖ (a)ₖ = (−1)ᵏ ∏_{l<k} (a² − l²)`. -/
private theorem ascPochhammer_eval_neg_mul_ascPochhammer_eval (a : ℂ) (k : ℕ) :
    (ascPochhammer ℂ k).eval (-a) * (ascPochhammer ℂ k).eval a =
      (-1) ^ k * ∏ l ∈ range k, (a ^ 2 - (l : ℂ) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, prod_range_succ, pow_succ]
    linear_combination ((-a + k) * (a + k)) * ih

/-- `(−n)ₖ (n + 2)ₖ = (−1)ᵏ ∏_{l<k} ((n + 1)² − (l + 1)²)`. -/
private theorem ascPochhammer_eval_neg_mul_ascPochhammer_eval_add_two (a : ℂ) (k : ℕ) :
    (ascPochhammer ℂ k).eval (-a) * (ascPochhammer ℂ k).eval (a + 2) =
      (-1) ^ k * ∏ l ∈ range k, ((a + 1) ^ 2 - ((l : ℂ) + 1) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, prod_range_succ, pow_succ]
    linear_combination ((-a + k) * (a + 2 + k)) * ih

/-- `2ᵏ (b/2)ₖ = ∏_{l<k} (2l + b)`. -/
private theorem two_pow_mul_ascPochhammer_eval_half (b : ℂ) (k : ℕ) :
    2 ^ k * (ascPochhammer ℂ k).eval (b / 2) = ∏ l ∈ range k, (2 * (l : ℂ) + b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, prod_range_succ, pow_succ, ← ih]
    ring

/-- **DLMF 15.9.5.** `Tₙ(x) = ₂F₁(−n, n; ½; (1 − x)/2)` for `n : ℕ` and every `x : ℂ`. -/
theorem chebyshevT_eq_ordinaryHypergeometric (n : ℕ) (x : ℂ) :
    (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval x = ₂F₁ (-n : ℂ) n (1 / 2) ((1 - x) / 2) := by
  rw [ordinaryHypergeometric_neg_nat_eq_sum,
    eval_eq_sum_iterate_derivative_eval_one _ (N := n + 1)
      (by rw [Polynomial.Chebyshev.natDegree_T]; simp)]
  refine sum_congr rfl fun k _ => ?_
  rw [Polynomial.Chebyshev.iterate_derivative_T_eval_one_eq_div]
  have hA := ascPochhammer_eval_neg_mul_ascPochhammer_eval (n : ℂ) k
  have hB := two_pow_mul_ascPochhammer_eval_half 1 k
  have hQ : ∏ l ∈ range k, (2 * (l : ℂ) + 1) ≠ 0 :=
    prod_ne_zero_iff.mpr fun l _ => by exact_mod_cast (by omega : 2 * l + 1 ≠ 0)
  have hkf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hP : (ascPochhammer ℂ k).eval (1 / 2 : ℂ) =
      (∏ l ∈ range k, (2 * (l : ℂ) + 1)) / 2 ^ k := by
    rw [eq_div_iff h2, mul_comm, hB]
  rw [hP, show ∀ u v w : ℂ, (k ! : ℂ)⁻¹ * u * v * w = (k ! : ℂ)⁻¹ * (u * v) * w by
    intros; ring, hA]
  push_cast
  field_simp
  rw [div_pow, show (1 - x) ^ k = (-1) ^ k * (x - 1) ^ k by rw [← mul_pow]; ring]
  field_simp
  ring_nf
  simp [pow_mul']

/-- **DLMF 15.9.6.** `Uₙ(x) = (n + 1) ₂F₁(−n, n + 2; 3/2; (1 − x)/2)` for `n : ℕ` and every
`x : ℂ`. -/
theorem chebyshevU_eq_ordinaryHypergeometric (n : ℕ) (x : ℂ) :
    (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval x =
      (n + 1) * ₂F₁ (-n : ℂ) (n + 2) (3 / 2) ((1 - x) / 2) := by
  rw [ordinaryHypergeometric_neg_nat_eq_sum,
    eval_eq_sum_iterate_derivative_eval_one _ (N := n + 1)
      (by rw [Polynomial.Chebyshev.natDegree_U]; omega), mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Polynomial.Chebyshev.iterate_derivative_U_eval_one_eq_div]
  have hA := ascPochhammer_eval_neg_mul_ascPochhammer_eval_add_two (n : ℂ) k
  have hB := two_pow_mul_ascPochhammer_eval_half 3 k
  have hQ : ∏ l ∈ range k, (2 * (l : ℂ) + 3) ≠ 0 :=
    prod_ne_zero_iff.mpr fun l _ => by exact_mod_cast (by omega : 2 * l + 3 ≠ 0)
  have hkf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hP : (ascPochhammer ℂ k).eval (3 / 2 : ℂ) =
      (∏ l ∈ range k, (2 * (l : ℂ) + 3)) / 2 ^ k := by
    rw [eq_div_iff h2, mul_comm, hB]
  rw [hP, show ∀ u v w : ℂ, (k ! : ℂ)⁻¹ * u * v * w = (k ! : ℂ)⁻¹ * (u * v) * w by
    intros; ring, hA]
  push_cast
  field_simp
  rw [div_pow, show (1 - x) ^ k = (-1) ^ k * (x - 1) ^ k by rw [← mul_pow]; ring]
  field_simp
  ring_nf
  simp [pow_mul']

/-- **DLMF 15.9.7.** Mathlib's shifted Legendre polynomial is the terminating Gauss series,
`P̃ₙ(y) = ₂F₁(−n, n + 1; 1; y)` for `n : ℕ` and every `y : ℂ`, with no further sign. At
`y = (1 − x)/2` both sides are the Legendre polynomial `Pₙ(x)`. -/
theorem shiftedLegendre_eval_eq_ordinaryHypergeometric (n : ℕ) (y : ℂ) :
    ((Polynomial.shiftedLegendre n).map (Int.castRingHom ℂ)).eval y =
      ₂F₁ (-n : ℂ) (n + 1) 1 y := by
  rw [ordinaryHypergeometric_neg_nat_eq_sum, eval_eq_sum_range'
    (Nat.lt_succ_of_le ((natDegree_map_le).trans (natDegree_shiftedLegendre n).le))]
  refine sum_congr rfl fun k _ => ?_
  have hneg : (ascPochhammer ℂ k).eval (-(n : ℂ)) = (-1) ^ k * k ! * n.choose k := by
    rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hpos : (ascPochhammer ℂ k).eval ((n : ℂ) + 1) = k ! * (n + k).choose k := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, ← ascPochhammer_eval_cast,
      ascPochhammer_nat_eq_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hkf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [coeff_map, coeff_shiftedLegendre, hneg, hpos, ascPochhammer_eval_one,
    Nat.choose_symm_add, eq_intCast]
  push_cast
  field_simp

end TauCeti
