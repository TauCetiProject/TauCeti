/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
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

/-- The power of a partial-correlation coordinate occurring in a natural power of one Cholesky
entry. It is `n` at the coordinate indexing that entry and zero elsewhere. -/
@[expose]
def partialCorrelationCholeskyEntryCoordinatePower (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) : ℕ :=
  if ij.1 = (i, k) then n else 0

/-- The defining formula for the coordinate power of one Cholesky entry. -/
theorem partialCorrelationCholeskyEntryCoordinatePower_def (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij =
      if ij.1 = (i, k) then n else 0 := rfl

/-- The residual power contributed by a natural power of one Cholesky entry. Every partial
correlation in the same row and a preceding column contributes `(1 - z²) ^ (n / 2)`. -/
@[expose]
def partialCorrelationCholeskyEntryResidualPower (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) : ℝ :=
  if ij.1.1 = i ∧ ij.1.2 < k then (n : ℝ) / 2 else 0

/-- The defining formula for the residual power of one Cholesky entry. -/
theorem partialCorrelationCholeskyEntryResidualPower_def (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryResidualPower i k n ij =
      if ij.1.1 = i ∧ ij.1.2 < k then (n : ℝ) / 2 else 0 := rfl

@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_apply (i k : Fin p) (n : ℕ)
    (hki : k < i) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ⟨(i, k), hki⟩ = n := by
  simp [partialCorrelationCholeskyEntryCoordinatePower]

@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_apply_of_ne (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (hij : ij.1 ≠ (i, k)) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij = 0 := by
  simp [partialCorrelationCholeskyEntryCoordinatePower, hij]

@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_of_eq_of_lt (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (hi : ij.1.1 = i) (hk : ij.1.2 < k) :
    partialCorrelationCholeskyEntryResidualPower i k n ij = (n : ℝ) / 2 := by
  simp [partialCorrelationCholeskyEntryResidualPower, hi, hk]

@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_of_not (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (h : ¬(ij.1.1 = i ∧ ij.1.2 < k)) :
    partialCorrelationCholeskyEntryResidualPower i k n ij = 0 := by
  simp [partialCorrelationCholeskyEntryResidualPower, h]

/-- Residual powers contributed by Cholesky entries are nonnegative. -/
theorem partialCorrelationCholeskyEntryResidualPower_nonneg (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    0 ≤ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  rw [partialCorrelationCholeskyEntryResidualPower_def]
  split_ifs
  · positivity
  · exact le_rfl

/-- The total natural coordinate power in a monomial of Cholesky entries. -/
@[expose]
def partialCorrelationCholeskyMonomialCoordinatePower
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) : ℕ :=
  ∑ q, partialCorrelationCholeskyEntryCoordinatePower q.1 q.2 (m q) ij

/-- The defining sum for the coordinate power in a Cholesky monomial. -/
theorem partialCorrelationCholeskyMonomialCoordinatePower_def
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialCoordinatePower m ij =
      ∑ q, partialCorrelationCholeskyEntryCoordinatePower q.1 q.2 (m q) ij := rfl

/-- The total residual power in a monomial of Cholesky entries. -/
@[expose]
def partialCorrelationCholeskyMonomialResidualPower
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) : ℝ :=
  ∑ q, partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij

/-- The defining sum for the residual power in a Cholesky monomial. -/
theorem partialCorrelationCholeskyMonomialResidualPower_def
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower m ij =
      ∑ q, partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij := rfl

/-- Residual powers in Cholesky monomials are nonnegative. -/
theorem partialCorrelationCholeskyMonomialResidualPower_nonneg
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    0 ≤ partialCorrelationCholeskyMonomialResidualPower m ij := by
  rw [partialCorrelationCholeskyMonomialResidualPower_def]
  exact Finset.sum_nonneg fun q _ ↦
    partialCorrelationCholeskyEntryResidualPower_nonneg q.1 q.2 (m q) ij

private theorem sqrt_pow_eq_rpow_half {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt x ^ n = x ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

private theorem pow_partialCorrelationCholeskyEntryFactor
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryFactor i k ij (z ij) ^ n =
      z ij ^ partialCorrelationCholeskyEntryCoordinatePower i k n ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  have hbase : 0 ≤ 1 - z ij ^ 2 :=
    (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))).le
  by_cases hc : ij.1.1 = i ∧ ij.1.2 = k
  · have hpair : ij.1 = (i, k) := Prod.ext hc.1 hc.2
    have hr : ¬(ij.1.1 = i ∧ ij.1.2 < k) := fun h ↦ (ne_of_lt h.2) hc.2
    rw [partialCorrelationCholeskyEntryCoordinatePower_def, ite_eq_left hpair,
      partialCorrelationCholeskyEntryResidualPower_def, ite_eq_right hr, Real.rpow_zero, mul_one,
      partialCorrelationCholeskyEntryFactor, ite_eq_left hc, ite_eq_right hr, mul_one]
  · have hpair : ij.1 ≠ (i, k) := fun h ↦ hc ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    by_cases hr : ij.1.1 = i ∧ ij.1.2 < k
    · rw [partialCorrelationCholeskyEntryCoordinatePower_def, ite_eq_right hpair,
        partialCorrelationCholeskyEntryResidualPower_def, ite_eq_left hr, pow_zero, one_mul,
        partialCorrelationCholeskyEntryFactor, ite_eq_right hc, ite_eq_left hr, one_mul]
      exact sqrt_pow_eq_rpow_half hbase n
    · rw [partialCorrelationCholeskyEntryCoordinatePower_def, ite_eq_right hpair,
        partialCorrelationCholeskyEntryResidualPower_def, ite_eq_right hr, pow_zero,
        Real.rpow_zero, one_mul, partialCorrelationCholeskyEntryFactor, ite_eq_right hc,
        ite_eq_right hr, mul_one, one_pow]

/-- On the open partial-correlation cube, a natural power of a lower-triangular Cholesky entry
factors into coordinate and residual powers. -/
theorem pow_partialCorrelationCholesky_eq_prod
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) (i k : Fin p) (n : ℕ)
    (hki : k ≤ i) :
    partialCorrelationCholesky z i k ^ n =
      ∏ ij, z ij ^ partialCorrelationCholeskyEntryCoordinatePower i k n ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  rw [← prod_partialCorrelationCholeskyEntryFactor z i k hki, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun ij _ ↦
    pow_partialCorrelationCholeskyEntryFactor hz i k n ij

/-- On the open partial-correlation cube, a joint monomial in lower-triangular Cholesky entries
factors coordinatewise. -/
theorem prod_pow_partialCorrelationCholesky_eq_prod
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1)
    (m : Fin p × Fin p → ℕ) (hm : ∀ q, m q ≠ 0 → q.2 ≤ q.1) :
    (∏ q, partialCorrelationCholesky z q.1 q.2 ^ m q) =
      ∏ ij, z ij ^ partialCorrelationCholeskyMonomialCoordinatePower m ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyMonomialResidualPower m ij := by
  have hentry (q : Fin p × Fin p) :
      partialCorrelationCholesky z q.1 q.2 ^ m q =
        ∏ ij, z ij ^ partialCorrelationCholeskyEntryCoordinatePower q.1 q.2 (m q) ij *
          (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij := by
    by_cases hq : m q = 0
    · simp [hq, partialCorrelationCholeskyEntryCoordinatePower_def,
        partialCorrelationCholeskyEntryResidualPower_def]
    · exact pow_partialCorrelationCholesky_eq_prod hz q.1 q.2 (m q) (hm q hq)
  calc
    (∏ q, partialCorrelationCholesky z q.1 q.2 ^ m q) =
        ∏ q, ∏ ij, z ij ^ partialCorrelationCholeskyEntryCoordinatePower q.1 q.2 (m q) ij *
          (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij :=
      Finset.prod_congr rfl fun q _ ↦ hentry q
    _ = ∏ ij, ∏ q, z ij ^ partialCorrelationCholeskyEntryCoordinatePower q.1 q.2 (m q) ij *
          (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij :=
      Finset.prod_comm
    _ = ∏ ij, z ij ^ partialCorrelationCholeskyMonomialCoordinatePower m ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyMonomialResidualPower m ij := by
      apply Finset.prod_congr rfl
      intro ij _
      rw [Finset.prod_mul_distrib, partialCorrelationCholeskyMonomialCoordinatePower_def,
        partialCorrelationCholeskyMonomialResidualPower_def,
        Finset.prod_pow_eq_pow_sum]
      congr 1
      exact (Real.rpow_sum_of_nonneg
        (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))).le
        (fun q _ ↦ partialCorrelationCholeskyEntryResidualPower_nonneg
          q.1 q.2 (m q) ij)).symm

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
  exact prod_pow_partialCorrelationCholesky_eq_prod hz m hm

/-- Every joint natural monomial in lower-triangular entries of the independent
centered-symmetric-Beta Cholesky construction is integrable. -/
theorem integrable_prod_pow_partialCorrelationCholesky_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij)
    (m : Fin p × Fin p → ℕ) (hm : ∀ q, m q ≠ 0 → q.2 ≤ q.1) :
    Integrable (fun z ↦ ∏ q, partialCorrelationCholesky z q.1 q.2 ^ m q)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) := by
  rw [integrable_congr (ae_prod_pow_partialCorrelationCholesky_eq_prod ha m hm)]
  apply integrable_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
    a (partialCorrelationCholeskyMonomialResidualPower m)
      (partialCorrelationCholeskyMonomialCoordinatePower m) ha
  intro ij
  exact add_pos_of_pos_of_nonneg (ha ij)
    (partialCorrelationCholeskyMonomialResidualPower_nonneg m ij)

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

private theorem ae_pow_partialCorrelationCholesky_eq_prod
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i k : Fin p) (n : ℕ)
    (hki : k ≤ i) :
    (fun z ↦ partialCorrelationCholesky z i k ^ n) =ᵐ[
      Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)]
      fun z ↦ ∏ ij, z ij ^ partialCorrelationCholeskyEntryCoordinatePower i k n ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  exact pow_partialCorrelationCholesky_eq_prod hz i k n hki

/-- Every natural power of an entry of the independent centered-symmetric-Beta Cholesky
construction is integrable. -/
theorem integrable_pow_partialCorrelationCholesky_pi_betaMeasure
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i k : Fin p) (n : ℕ) :
    Integrable (fun z ↦ partialCorrelationCholesky z i k ^ n)
      (Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) := by
  let _ (ij : strictLowerTriangle p) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  by_cases hki : k ≤ i
  · rw [integrable_congr (ae_pow_partialCorrelationCholesky_eq_prod ha i k n hki)]
    apply integrable_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
      a (partialCorrelationCholeskyEntryResidualPower i k n)
        (partialCorrelationCholeskyEntryCoordinatePower i k n) ha
    intro ij
    exact add_pos_of_pos_of_nonneg (ha ij)
      (partialCorrelationCholeskyEntryResidualPower_nonneg i k n ij)
  · have hik : i < k := lt_of_not_ge hki
    simp [partialCorrelationCholesky_apply_of_lt _ hik]

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
  · rw [integral_congr_ae (ae_pow_partialCorrelationCholesky_eq_prod ha i k n hki)]
    apply integral_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure
      a (partialCorrelationCholeskyEntryResidualPower i k n)
        (partialCorrelationCholeskyEntryCoordinatePower i k n) ha
    intro ij
    exact add_pos_of_pos_of_nonneg (ha ij)
      (partialCorrelationCholeskyEntryResidualPower_nonneg i k n ij)
  · subst n
    simp
  · have hik : i < k := lt_of_not_ge hki
    simp [partialCorrelationCholesky_apply_of_lt _ hik, hn]

end TauCeti.Probability
