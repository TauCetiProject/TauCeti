/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Powers
public import TauCeti.Probability.Distributions.Beta.Symmetric

/-!
# Moments of partial-correlation Cholesky factors

Products of natural powers of entries of the partial-correlation Cholesky factor split into
one-dimensional factors. Each partial correlation contributes a natural coordinate power and a
nonnegative half-integer power of its residual variance. Under independent centered symmetric
Beta laws, all such joint monomials are integrable and their moments are finite products of Beta
quotients.

These joint moments are the building blocks for mixed moments of LKJ correlation matrices: after
expanding `R = L Lᵀ`, each summand is a product of powers of Cholesky entries.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace TauCeti.Probability

variable {p : ℕ}

/-- The coordinatewise factorization of a lower-triangular Cholesky monomial holds almost
everywhere under independent centered symmetric Beta laws. -/
theorem ae_prod_pow_partialCorrelationCholesky_eq_prod
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (m : Fin p × Fin p → ℕ) (hm : ∀ q, m q ≠ 0 → q.2 ≤ q.1) :
    (fun z ↦ ∏ q, partialCorrelationCholesky z q.1 q.2 ^ m q) =ᵐ[
      Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)]
      fun z ↦ ∏ ij, z ij ^ partialCorrelationCholeskyMonomialCoordinatePower m ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyMonomialResidualPower m ij := by
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  exact prod_pow_partialCorrelationCholesky_eq_prod (fun ij ↦ (hz ij).le) m hm

/-- Every joint natural monomial in lower-triangular entries of the independent
centered-symmetric-Beta Cholesky construction is integrable. -/
theorem integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (m : Fin p × Fin p → ℕ) :
    Integrable (fun z ↦ ∏ q, partialCorrelationCholesky z q.1 q.2 ^ m q)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) := by
  classical
  by_cases hm : ∀ q, m q ≠ 0 → q.2 ≤ q.1
  · rw [integrable_congr (ae_prod_pow_partialCorrelationCholesky_eq_prod ha m hm)]
    apply integrable_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
      a (partialCorrelationCholeskyMonomialResidualPower m)
        (partialCorrelationCholeskyMonomialCoordinatePower m) ha
    intro ij
    exact add_pos_of_pos_of_nonneg (ha ij)
      (partialCorrelationCholeskyMonomialResidualPower_nonneg m ij)
  · simp only [not_forall] at hm
    obtain ⟨q, hq⟩ := hm
    simp only [not_le] at hq
    have hzero : (fun z ↦ ∏ q, partialCorrelationCholesky z q.1 q.2 ^ m q) =
        fun _ ↦ 0 := by
      funext z
      apply Finset.prod_eq_zero (Finset.mem_univ q)
      simp [partialCorrelationCholesky_apply_of_lt z hq.2, hq.1]
    rw [hzero]
    exact integrable_zero _ _ _

/-- Joint natural moments of lower-triangular entries in the independent
centered-symmetric-Beta Cholesky construction. -/
theorem integral_prod_pow_partialCorrelationCholesky_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (m : Fin p × Fin p → ℕ) (hm : ∀ q, m q ≠ 0 → q.2 ≤ q.1) :
    ∫ z, ∏ q, partialCorrelationCholesky z q.1 q.2 ^ m q
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) =
      ∏ ij, if Even (partialCorrelationCholeskyMonomialCoordinatePower m ij) then
        beta ((((partialCorrelationCholeskyMonomialCoordinatePower m ij : ℕ) : ℝ) + 1) / 2)
            (a ij + partialCorrelationCholeskyMonomialResidualPower m ij) /
          beta (1 / 2) (a ij)
      else 0 := by
  rw [integral_congr_ae (ae_prod_pow_partialCorrelationCholesky_eq_prod ha m hm)]
  apply integral_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
    a (partialCorrelationCholeskyMonomialResidualPower m)
      (partialCorrelationCholeskyMonomialCoordinatePower m) ha
  intro ij
  exact add_pos_of_pos_of_nonneg (ha ij)
    (partialCorrelationCholeskyMonomialResidualPower_nonneg m ij)

private theorem prod_pow_partialCorrelationCholesky_single
    (z : strictLowerTriangle p → ℝ) (i k : Fin p) (n : ℕ) :
    (∏ q, partialCorrelationCholesky z q.1 q.2 ^ Pi.single (i, k) n q) =
      partialCorrelationCholesky z i k ^ n := by
  classical
  conv_rhs =>
    rw [← Pi.single_eq_same (M := fun _ : Fin p × Fin p ↦ ℕ) (i, k) n]
  apply Fintype.prod_eq_single (i, k)
  · intro q hq
    simp [Pi.single_eq_of_ne hq]

/-- Every natural power of an entry of the independent centered-symmetric-Beta Cholesky
construction is integrable. -/
theorem integrable_pow_partialCorrelationCholesky_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i k : Fin p) (n : ℕ) :
    Integrable (fun z ↦ partialCorrelationCholesky z i k ^ n)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) := by
  simpa only [prod_pow_partialCorrelationCholesky_single] using
    integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha (Pi.single (i, k) n)

/-- Natural moments of an entry in the independent centered-symmetric-Beta Cholesky construction.
At or below the diagonal the value is the product of the corresponding weighted Beta moments;
above the diagonal it is zero at positive orders and one at order zero. -/
theorem integral_pow_partialCorrelationCholesky_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i k : Fin p) (n : ℕ) :
    ∫ z, partialCorrelationCholesky z i k ^ n
      ∂(Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) =
      if k ≤ i then
        ∏ ij, if Even (partialCorrelationCholeskyEntryCoordinatePower i k n ij) then
          beta ((((partialCorrelationCholeskyEntryCoordinatePower i k n ij : ℕ) : ℝ) + 1) / 2)
              (a ij + partialCorrelationCholeskyEntryResidualPower i k n ij) /
            beta (1 / 2) (a ij)
        else 0
      else if n = 0 then 1 else 0 := by
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  split_ifs with hki hn
  · have hm : ∀ q : Fin p × Fin p,
        Pi.single (M := fun _ : Fin p × Fin p ↦ ℕ) (i, k) n q ≠ 0 → q.2 ≤ q.1 := by
      intro q hq
      have hqik : q = (i, k) := by
        by_contra hne
        apply hq
        simp [hne]
      simpa [hqik] using hki
    simpa only [prod_pow_partialCorrelationCholesky_single,
      partialCorrelationCholeskyMonomialCoordinatePower_single,
      partialCorrelationCholeskyMonomialResidualPower_single] using
      integral_prod_pow_partialCorrelationCholesky_pi_betaMeasure ha (Pi.single (i, k) n) hm
  · subst n
    simp
  · have hik : i < k := lt_of_not_ge hki
    simp [partialCorrelationCholesky_apply_of_lt _ hik, hn]

end TauCeti.Probability
