/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
public import TauCeti.Analysis.Matrix.PartialCorrelation.Polynomial
public import TauCeti.Probability.Distributions.Beta.Polynomial

/-!
# Finite Beta-product expansions for LKJ mixed entry moments

Expand a monomial in correlation-matrix entries through the partial-correlation Gram matrix,
treating coordinates and residual square roots as separate polynomial variables. Each
monomial in the resulting polynomial has an expectation given by a product of Beta quotients.
Thus the polynomial's finite support gives an exact, finite formula for every natural mixed
entry moment. Ordered-pair exponents are allowed, so symmetry need not be resolved beforehand.
The empty matrix and the zeroth monomial are included.

This uses the independent centered-Beta construction `map_coe_lkjMeasure`, not individual
Cholesky-entry moments: entries in a Cholesky row are not generally independent.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace TauCeti.Probability

/-- Every natural mixed entry monomial is absolutely integrable under an LKJ measure,
including the zero measure at nonpositive shape. -/
theorem integrable_prod_pow_coe_apply_lkjMeasure {p : ℕ} {η : ℝ}
    (n : Fin p → Fin p → ℕ) :
    Integrable (fun R ↦ ∏ i, ∏ j, (R.val i j) ^ n i j) (lkjMeasure p η) := by
  by_cases hη : 0 < η
  · have hcont : Continuous (fun R : Matrix (Fin p) (Fin p) ℝ ↦
        ∏ i, ∏ j, R i j ^ n i j) := by fun_prop
    apply (integrable_map_measure (μ := lkjMeasure p η) (f := Subtype.val)
      (g := fun R : Matrix (Fin p) (Fin p) ℝ ↦ ∏ i, ∏ j, R i j ^ n i j)
      hcont.aestronglyMeasurable (by fun_prop)).mp
    rw [map_coe_lkjMeasure hη,
      integrable_map_measure hcont.aestronglyMeasurable (by fun_prop)]
    simpa only [Function.comp_def, ← eval_partialCorrelationGramMonomialPolynomial] using
      integrable_eval_sumElim_sqrt_one_sub_sq_pi_centered_betaMeasure _
        (lkjPartialCorrelationShape_pos hη) (partialCorrelationGramMonomialPolynomial p n)
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

/-- Every natural mixed entry moment of a valid LKJ law equals a finite sum of Beta products.
The exponents in each term are the coefficients' monomial indices in the explicit Gram
expansion. Odd partial-correlation exponents vanish; residual exponents enter as half-integers. -/
theorem integral_prod_pow_coe_apply_lkjMeasure {p : ℕ} {η : ℝ} (hη : 0 < η)
    (n : Fin p → Fin p → ℕ) :
    ∫ R, (∏ i, ∏ j, (R.val i j) ^ n i j) ∂lkjMeasure p η =
      ∑ d ∈ (partialCorrelationGramMonomialPolynomial p n).support,
        (partialCorrelationGramMonomialPolynomial p n).coeff d * ∏ ij : strictLowerTriangle p,
          if Even (d (Sum.inl ij)) then
            beta (((d (Sum.inl ij) : ℝ) + 1) / 2)
                (lkjPartialCorrelationShape p η ij + (d (Sum.inr ij) : ℝ) / 2) /
              beta (1 / 2) (lkjPartialCorrelationShape p η ij) else 0 := by
  have hmap := map_coe_lkjMeasure (p := p) hη
  have hcont : Continuous (fun R : Matrix (Fin p) (Fin p) ℝ ↦
      ∏ i, ∏ j, R i j ^ n i j) := by fun_prop
  have htransfer :
      (∫ R, (∏ i, ∏ j, (R.val i j) ^ n i j) ∂lkjMeasure p η) =
        ∫ z : strictLowerTriangle p → ℝ,
          MvPolynomial.eval (Sum.elim z (fun ij ↦ Real.sqrt (1 - z ij ^ 2)))
            (partialCorrelationGramMonomialPolynomial p n)
          ∂(Measure.pi fun ij ↦
            (betaMeasure (lkjPartialCorrelationShape p η ij)
              (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) := by
    rw [← integral_map (φ := Subtype.val)
      (f := fun R : Matrix (Fin p) (Fin p) ℝ ↦ ∏ i, ∏ j, R i j ^ n i j)
      (by fun_prop) hcont.aestronglyMeasurable, hmap,
      integral_map (by fun_prop) hcont.aestronglyMeasurable]
    simp only [eval_partialCorrelationGramMonomialPolynomial]
  rw [htransfer]
  exact integral_eval_sumElim_sqrt_one_sub_sq_pi_centered_betaMeasure _
    (lkjPartialCorrelationShape_pos hη) _

end TauCeti.Probability
