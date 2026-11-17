/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Complex polynomials with roots in a disc

Let `P = ∏ i, (X - bᵢ)` be the monic complex polynomial with roots `b : ι → ℂ`, indexed by a
finite type of cardinality `m`, and suppose that every root lies in the closed disc of radius
`ρ` about the origin. This file records the elementary bounds on `P` and `P'` that hold uniformly
for all such `P`, depending only on `m` and `ρ`, and the continuity of `P(z)` and `P'(z)` in the
roots. Such bounds make estimates that depend on a polynomial uniform over a compact family of
root configurations, repeated roots included.

* `Polynomial.pow_le_norm_eval_prod_X_sub_C`: `|P(z)| ≥ (|z| - ρ)ᵐ` for `|z| ≥ ρ`, since each
  factor is at least `|z| - ρ`.
* `Polynomial.norm_eval_derivative_prod_X_sub_C_le`: `|P'(z)| ≤ m (|z| + ρ)ᵐ⁻¹` for every `z`.
* `Polynomial.norm_eval_derivative_prod_X_sub_C_mul_le`: `|P'(z)| (|z| - ρ) ≤ m |P(z)|` for
  `|z| ≥ ρ`. Since `P'(z) = ∑ᵢ ∏_{j ≠ i} (z - bⱼ)`, each term times `|z| - ρ` is at most `|P(z)|`;
  this is the bound `|P'/P| ≤ m / (|z| - ρ)` on the logarithmic derivative, without dividing.
* `Polynomial.continuous_eval_prod_X_sub_C`, `Polynomial.continuous_eval_derivative_prod_X_sub_C`:
  for fixed `z`, the values `P(z)` and `P'(z)` are continuous functions of the roots.
-/

public section

namespace Polynomial

variable {ι : Type*} [Fintype ι]

/-- The derivative of `∏ i, (X - bᵢ)` evaluated at `z` is `∑ᵢ ∏_{j ≠ i} (z - bⱼ)`. -/
private theorem eval_derivative_prod_X_sub_C [DecidableEq ι] (b : ι → ℂ) (z : ℂ) :
    (∏ i, (X - C (b i))).derivative.eval z = ∑ i, ∏ j ∈ Finset.univ.erase i, (z - b j) := by
  simp [derivative_prod_finset, eval_finsetSum, eval_prod]

/-- **A lower bound outside the disc of roots.** If every root of `P = ∏ i, (X - bᵢ)` has modulus
at most `ρ ≤ |z|`, then `(|z| - ρ)ᵐ ≤ |P(z)|`, where `m` is the number of roots. -/
theorem pow_le_norm_eval_prod_X_sub_C {b : ι → ℂ} {ρ : ℝ} (hb : ∀ i, ‖b i‖ ≤ ρ) {z : ℂ}
    (hz : ρ ≤ ‖z‖) : (‖z‖ - ρ) ^ Fintype.card ι ≤ ‖(∏ i, (X - C (b i))).eval z‖ := by
  rw [eval_prod, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ sub_nonneg.mpr hz) fun i _ ↦ ?_
  simpa using (sub_le_sub_left (hb i) _).trans (norm_sub_norm_le z (b i))

/-- **A bound on the derivative.** If every root of `P = ∏ i, (X - bᵢ)` has modulus at most `ρ`,
then `|P'(z)| ≤ m (|z| + ρ)ᵐ⁻¹`, where `m` is the number of roots. -/
theorem norm_eval_derivative_prod_X_sub_C_le {b : ι → ℂ} {ρ : ℝ} (hb : ∀ i, ‖b i‖ ≤ ρ) (z : ℂ) :
    ‖(∏ i, (X - C (b i))).derivative.eval z‖ ≤
      Fintype.card ι * (‖z‖ + ρ) ^ (Fintype.card ι - 1) := by
  classical
  rw [eval_derivative_prod_X_sub_C]
  refine (norm_sum_le _ _).trans ?_
  rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  rw [norm_prod, ← Finset.card_erase_of_mem hi, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    fun j _ ↦ (norm_sub_le z (b j)).trans (by linarith [hb j])

/-- **The logarithmic derivative outside the disc of roots.** If every root of
`P = ∏ i, (X - bᵢ)` has modulus at most `ρ ≤ |z|`, then `|P'(z)| (|z| - ρ) ≤ m |P(z)|`, where `m`
is the number of roots. -/
theorem norm_eval_derivative_prod_X_sub_C_mul_le {b : ι → ℂ} {ρ : ℝ} (hb : ∀ i, ‖b i‖ ≤ ρ)
    {z : ℂ} (hz : ρ ≤ ‖z‖) :
    ‖(∏ i, (X - C (b i))).derivative.eval z‖ * (‖z‖ - ρ) ≤
      Fintype.card ι * ‖(∏ i, (X - C (b i))).eval z‖ := by
  classical
  rw [eval_derivative_prod_X_sub_C]
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  have hρ : 0 ≤ ‖z‖ - ρ := sub_nonneg.mpr hz
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) hρ).trans ?_
  rw [Finset.sum_mul, ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  rw [← Finset.prod_erase_mul _ _ hi, norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((sub_le_sub_left (hb i) _).trans (norm_sub_norm_le z (b i))) (norm_nonneg _)

/-- The value at a fixed point of the polynomial `∏ i, (X - bᵢ)` is continuous in the roots. -/
theorem continuous_eval_prod_X_sub_C (z : ℂ) :
    Continuous fun b : ι → ℂ ↦ (∏ i, (X - C (b i))).eval z := by
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  fun_prop

/-- The value at a fixed point of the derivative of `∏ i, (X - bᵢ)` is continuous in the
roots. -/
theorem continuous_eval_derivative_prod_X_sub_C (z : ℂ) :
    Continuous fun b : ι → ℂ ↦ (∏ i, (X - C (b i))).derivative.eval z := by
  classical
  simp_rw [eval_derivative_prod_X_sub_C]
  fun_prop

end Polynomial
