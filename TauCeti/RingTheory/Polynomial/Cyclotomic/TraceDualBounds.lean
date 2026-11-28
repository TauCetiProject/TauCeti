/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Expand
import TauCeti.Analysis.Polynomial.CoeffBound

/-!
# Bounds for cyclotomic trace-dual coefficients

When the level is enlarged without introducing new primes, its cyclotomic polynomial is an
expansion of the base polynomial and retains its coefficient length.
`TauCeti.norm_coeff_cyclotomic_mul_divByMonic_X_sub_C_le` bounds the quotient coefficients using
that length. `TauCeti.norm_mul_cyclotomic_divByMonic_coeff_div_derivative_le` also accounts for
the derivative in the denominator of the trace-dual basis, using
`TauCeti.norm_eval_derivative_cyclotomic_mul`. Summing the squared bounds gives
`TauCeti.mul_one_add_sum_norm_sq_cyclotomic_add_re_le`, which bounds the length expression of the
corrected frame in terms of derivatives at the base level.

The trace-dual application follows `New.Parameters.norm_phi_coeff_cyclotomicQuotient_le` and
`New.Data.le_b_of_eq_dualResolutionFactor` in
`grh/src/New/Derivatives/Vacuum/ShortVectors.lean` of
lsernau/grh-lean at revision `72fead1`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Polynomial

namespace TauCeti

/-- At a cyclotomic level `n * m` with no new prime divisors, the coefficients after division
by `X - C z` for `‖z‖ ≤ 1` are bounded in norm by `2 ^ φ(n)`. -/
theorem norm_coeff_cyclotomic_mul_divByMonic_X_sub_C_le {n m : ℕ}
    (h : m.primeFactors ⊆ n.primeFactors) {z : ℂ} (hz : ‖z‖ ≤ 1) (i : ℕ) :
    ‖(cyclotomic (n * m) ℂ /ₘ (X - C z)).coeff i‖ ≤ (2 : ℝ) ^ n.totient := by
  refine (norm_coeff_divByMonic_X_sub_C_le_l1Norm _ hz i).trans ?_
  obtain rfl | hm := eq_or_ne m 0
  · simp only [mul_zero, cyclotomic_zero, l1Norm_one]
    exact one_le_pow₀ one_le_two
  rw [← TauCeti.cyclotomic_expand_eq_cyclotomic_of_primeFactors_subset ℂ hm h,
    l1Norm_expand _ hm.bot_lt]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn),
    ← Complex.card_primitiveRoots n, ← Finset.prod_const]
  exact (l1Norm_prod_X_sub_C_le _ id (M := fun _ ↦ 1) fun w hw ↦
    ((mem_primitiveRoots hn.bot_lt).mp hw).norm'_eq_one hn |>.le).trans_eq (by norm_num)

/-- On the unit circle, bound the scaled quotient coefficient divided by the derivative at
level `n * m`. At a primitive root this is the scaled trace-dual coefficient. The denominator
retains the factor `m` from the derivative, while the numerator bound depends only on `n`. -/
theorem norm_mul_cyclotomic_divByMonic_coeff_div_derivative_le
    {n m : ℕ} (h : m.primeFactors ⊆ n.primeFactors) {z : ℂ} (hz : ‖z‖ = 1) (a : ℂ) (i : ℕ) :
    ‖a * (cyclotomic (n * m) ℂ /ₘ (X - C z)).coeff i /
        (cyclotomic (n * m) ℂ).derivative.eval z‖ ≤
      ‖a‖ * (2 : ℝ) ^ n.totient / (m * ‖(cyclotomic n ℂ).derivative.eval (z ^ m)‖) := by
  rw [norm_div, norm_mul, TauCeti.norm_eval_derivative_cyclotomic_mul h hz]
  gcongr
  exact norm_coeff_cyclotomic_mul_divByMonic_X_sub_C_le h hz.le i

/-- Bound the corrected frame length from the trace-dual basis of level `n * m` in terms of
the derivatives at level `n`. The family `z` gives the images of the primitive root under
the chosen embeddings, and `a` is the common scaling of the trace-dual vectors. The estimate
only requires the images to be on the unit circle. -/
theorem mul_one_add_sum_norm_sq_cyclotomic_add_re_le {ι : Type*} [Fintype ι] {n m : ℕ}
    (h : m.primeFactors ⊆ n.primeFactors) (z : ι → ℂ) (hz : ∀ t, ‖z t‖ = 1) (a : ℂ) :
    (n * m : ℕ) * (1 + ∑ t, ∑ i : Fin (n * m).totient,
      ‖a * (cyclotomic (n * m) ℂ /ₘ (X - C (z t))).coeff i /
        (cyclotomic (n * m) ℂ).derivative.eval (z t)‖ ^ 2) + 2 * a.re ≤
      (n * m : ℕ) * (1 + (n * m).totient * ∑ t,
        (‖a‖ * (2 : ℝ) ^ n.totient / (m * ‖(cyclotomic n ℂ).derivative.eval (z t ^ m)‖)) ^ 2) +
      2 * ‖a‖ := by
  have hs :
      (∑ t, ∑ i : Fin (n * m).totient,
        ‖a * (cyclotomic (n * m) ℂ /ₘ (X - C (z t))).coeff i /
          (cyclotomic (n * m) ℂ).derivative.eval (z t)‖ ^ 2) ≤
      (n * m).totient * ∑ t,
        (‖a‖ * (2 : ℝ) ^ n.totient / (m * ‖(cyclotomic n ℂ).derivative.eval (z t ^ m)‖)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    calc
      _ ≤ ∑ _i : Fin (n * m).totient,
          (‖a‖ * (2 : ℝ) ^ n.totient / (m * ‖(cyclotomic n ℂ).derivative.eval (z t ^ m)‖)) ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _)
          (norm_mul_cyclotomic_divByMonic_coeff_div_derivative_le h (hz t) a i) 2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  gcongr
  exact Complex.re_le_norm a

end TauCeti
