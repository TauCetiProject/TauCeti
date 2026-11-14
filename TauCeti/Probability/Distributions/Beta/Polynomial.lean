/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Symmetric
public import TauCeti.Analysis.MvPolynomial.Sqrt

/-!
# Polynomial moments of centered Beta coordinates and their residuals

A polynomial in independent centered symmetric Beta coordinates `z i` and their residual
square roots `√(1 - z i ^ 2)` has an absolutely convergent expectation. Expanding the polynomial
into monomials evaluates that expectation as a finite sum of products of Beta quotients.
The left summand of the variable type indexes coordinates, and the right summand indexes
residual square roots. This allows polynomial matrix constructions involving both kinds of
factors to be integrated without manually collecting exponents.

The scalar integration is supplied by
`integral_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem integrable_eval_sumElim_sqrt_one_sub_sq_monomial (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (n : (ι ⊕ ι) →₀ ℕ) (c : ℝ) :
    Integrable (fun z : ι → ℝ ↦
      MvPolynomial.eval (Sum.elim z (fun i ↦ Real.sqrt (1 - z i ^ 2)))
        (MvPolynomial.monomial n c))
      (Measure.pi fun i ↦ (betaMeasure (a i) (a i)).map (fun x ↦ -1 + 2 * x)) := by
  apply Integrable.congr
    ((integrable_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure a
      (fun i ↦ (n (Sum.inr i) : ℝ) / 2) (fun i ↦ n (Sum.inl i)) ha
      (fun i ↦ add_pos_of_pos_of_nonneg (ha i) (by positivity))).const_mul c)
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  exact (MvPolynomial.eval_sumElim_sqrt_one_sub_sq_monomial n c z fun i ↦ (hz i).le).symm

/-- Every polynomial in independent centered symmetric Beta coordinates and their residual
square roots is integrable, including for an empty coordinate type. -/
theorem integrable_eval_sumElim_sqrt_one_sub_sq_pi_centered_betaMeasure (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (P : MvPolynomial (ι ⊕ ι) ℝ) :
    Integrable (fun z : ι → ℝ ↦
      MvPolynomial.eval (Sum.elim z (fun i ↦ Real.sqrt (1 - z i ^ 2))) P)
      (Measure.pi fun i ↦ (betaMeasure (a i) (a i)).map (fun x ↦ -1 + 2 * x)) := by
  conv in MvPolynomial.eval _ P => rw [P.as_sum]
  simp only [MvPolynomial.eval_sum]
  exact integrable_finsetSum _ fun n _ ↦ integrable_eval_sumElim_sqrt_one_sub_sq_monomial a ha n _

/-- Expand a polynomial in independent centered symmetric Beta coordinates and their residual
square roots into a finite sum of Beta products. Odd coordinate exponents contribute zero;
residual square-root exponents contribute half their natural degree to the second Beta shape. -/
theorem integral_eval_sumElim_sqrt_one_sub_sq_pi_centered_betaMeasure (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (P : MvPolynomial (ι ⊕ ι) ℝ) :
    ∫ z : ι → ℝ,
      MvPolynomial.eval (Sum.elim z (fun i ↦ Real.sqrt (1 - z i ^ 2))) P
      ∂(Measure.pi fun i ↦ (betaMeasure (a i) (a i)).map (fun x ↦ -1 + 2 * x)) =
      ∑ n ∈ P.support, P.coeff n * ∏ i,
        if Even (n (Sum.inl i)) then
          beta (((n (Sum.inl i) : ℝ) + 1) / 2) (a i + (n (Sum.inr i) : ℝ) / 2) /
            beta (1 / 2) (a i) else 0 := by
  conv_lhs =>
    arg 2
    ext z
    rw [P.as_sum, MvPolynomial.eval_sum]
  rw [integral_finsetSum _ fun n _ ↦ integrable_eval_sumElim_sqrt_one_sub_sq_monomial a ha n _]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_congr_ae (by
    filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
    exact MvPolynomial.eval_sumElim_sqrt_one_sub_sq_monomial n (P.coeff n) z fun i ↦ (hz i).le),
    integral_const_mul]
  congr 1
  exact integral_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure a
    (fun i ↦ (n (Sum.inr i) : ℝ) / 2) (fun i ↦ n (Sum.inl i)) ha
    (fun i ↦ add_pos_of_pos_of_nonneg (ha i) (by positivity))

end TauCeti.Probability
