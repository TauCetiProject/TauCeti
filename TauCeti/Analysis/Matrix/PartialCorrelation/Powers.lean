/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic

/-!
# Powers of partial-correlation Cholesky entries

Natural powers of entries of the partial-correlation Cholesky factor split into coordinate and
residual powers of the individual partial correlations. This file records the deterministic
factorization used by moment calculations.
-/

public section

noncomputable section

open Real
open scoped BigOperators

namespace TauCeti.Probability

variable {p : ℕ}

/-- The contribution of one partial-correlation coordinate to an entry of the triangular
factor. -/
def partialCorrelationCholeskyEntryFactor (i k : Fin p) (ij : strictLowerTriangle p)
    (x : ℝ) : ℝ :=
  (if ij.1.1 = i ∧ ij.1.2 = k then x else 1) *
    (if ij.1.1 = i ∧ ij.1.2 < k then Real.sqrt (1 - x ^ 2) else 1)

/-- The defining formula for one coordinate factor of a Cholesky entry. -/
theorem partialCorrelationCholeskyEntryFactor_def (i k : Fin p)
    (ij : strictLowerTriangle p) (x : ℝ) :
    partialCorrelationCholeskyEntryFactor i k ij x =
      (if ij.1.1 = i ∧ ij.1.2 = k then x else 1) *
        (if ij.1.1 = i ∧ ij.1.2 < k then Real.sqrt (1 - x ^ 2) else 1) := by
  rw [partialCorrelationCholeskyEntryFactor]

@[simp]
theorem partialCorrelationCholeskyEntryFactor_of_coordinate (i k : Fin p)
    (ij : strictLowerTriangle p) (x : ℝ) (h : ij.1.1 = i ∧ ij.1.2 = k) :
    partialCorrelationCholeskyEntryFactor i k ij x = x := by
  have hr : ¬(ij.1.1 = i ∧ ij.1.2 < k) := fun h' ↦ (ne_of_lt h'.2) h.2
  rw [partialCorrelationCholeskyEntryFactor_def, ite_eq_left h, ite_eq_right hr, mul_one]

@[simp]
theorem partialCorrelationCholeskyEntryFactor_of_residual (i k : Fin p)
    (ij : strictLowerTriangle p) (x : ℝ) (h : ij.1.1 = i ∧ ij.1.2 < k) :
    partialCorrelationCholeskyEntryFactor i k ij x = Real.sqrt (1 - x ^ 2) := by
  have hc : ¬(ij.1.1 = i ∧ ij.1.2 = k) := fun h' ↦ (ne_of_lt h.2) h'.2
  rw [partialCorrelationCholeskyEntryFactor_def, ite_eq_right hc, ite_eq_left h, one_mul]

@[simp]
theorem partialCorrelationCholeskyEntryFactor_of_other (i k : Fin p)
    (ij : strictLowerTriangle p) (x : ℝ)
    (hc : ¬(ij.1.1 = i ∧ ij.1.2 = k)) (hr : ¬(ij.1.1 = i ∧ ij.1.2 < k)) :
    partialCorrelationCholeskyEntryFactor i k ij x = 1 := by
  rw [partialCorrelationCholeskyEntryFactor_def, ite_eq_right hc, ite_eq_right hr, mul_one]

/-- A coordinate factor of a Cholesky entry has absolute value at most one on the closed
partial-correlation interval. -/
theorem abs_partialCorrelationCholeskyEntryFactor_le_one (i k : Fin p)
    (ij : strictLowerTriangle p) {x : ℝ} (hx : |x| ≤ 1) :
    |partialCorrelationCholeskyEntryFactor i k ij x| ≤ 1 := by
  have hs' : Real.sqrt (1 - x ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg x]
  by_cases hc : ij.1.1 = i ∧ ij.1.2 = k
  · rw [partialCorrelationCholeskyEntryFactor_of_coordinate i k ij x hc]
    exact hx
  by_cases hr : ij.1.1 = i ∧ ij.1.2 < k
  · rw [partialCorrelationCholeskyEntryFactor_of_residual i k ij x hr,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hs'
  · rw [partialCorrelationCholeskyEntryFactor_of_other i k ij x hc hr, abs_one]

/-- A partial correlation from another row contributes the identity coordinate factor. -/
theorem partialCorrelationCholeskyEntryFactor_of_other_row (i k : Fin p)
    (ij : strictLowerTriangle p) (hi : ij.1.1 ≠ i) (x : ℝ) :
    partialCorrelationCholeskyEntryFactor i k ij x = 1 := by
  simp [hi]

/-- A lower-triangular entry is the product of its coordinatewise factors. -/
theorem prod_partialCorrelationCholeskyEntryFactor (z : strictLowerTriangle p → ℝ)
    (i k : Fin p) (hki : k ≤ i) :
    (∏ ij, partialCorrelationCholeskyEntryFactor i k ij (z ij)) =
      partialCorrelationCholesky z i k := by
  simp only [partialCorrelationCholeskyEntryFactor_def, Finset.prod_mul_distrib]
  have hr : (∏ ij : strictLowerTriangle p,
      if ij.1.1 = i ∧ ij.1.2 < k then Real.sqrt (1 - z ij ^ 2) else 1) =
      ∏ ij : strictLowerTriangle p with ij.1.1 = i ∧ ij.1.2 < k,
        Real.sqrt (1 - z ij ^ 2) := by rw [Finset.prod_filter]
  rw [hr]
  rcases hki.eq_or_lt with hki | hki
  · subst k
    rw [partialCorrelationCholesky_apply_self]
    have hnone : ∀ ij : strictLowerTriangle p, ¬(ij.1.1 = i ∧ ij.1.2 = i) := by
      intro ij h
      have := ij.2
      simp_all
    simp only [hnone, ↓reduceIte, Finset.prod_const_one, one_mul]
    congr 1
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
    exact fun h ↦ h ▸ ij.2
  · rw [partialCorrelationCholesky_apply_of_gt z hki]
    congr 1
    have heq (ij : strictLowerTriangle p) :
        (ij.1.1 = i ∧ ij.1.2 = k) ↔ ij = ⟨(i, k), hki⟩ := by
      simp only [Subtype.ext_iff, Prod.ext_iff]
    simp_rw [heq]
    simp

/-- The power of a partial-correlation coordinate occurring in a natural power of one Cholesky
entry. It is `n` at the coordinate indexing that entry and zero elsewhere. -/
def partialCorrelationCholeskyEntryCoordinatePower (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) : ℕ :=
  if ij.1 = (i, k) then n else 0

/-- The defining formula for the coordinate power of one Cholesky entry. -/
theorem partialCorrelationCholeskyEntryCoordinatePower_def (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij =
      if ij.1 = (i, k) then n else 0 := by
  rw [partialCorrelationCholeskyEntryCoordinatePower]

/-- The residual power contributed by a natural power of one Cholesky entry. Every partial
correlation in the same row and a preceding column contributes `(1 - z²) ^ (n / 2)`. -/
def partialCorrelationCholeskyEntryResidualPower (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) : ℝ :=
  if ij.1.1 = i ∧ ij.1.2 < k then (n : ℝ) / 2 else 0

/-- The defining formula for the residual power of one Cholesky entry. -/
theorem partialCorrelationCholeskyEntryResidualPower_def (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryResidualPower i k n ij =
      if ij.1.1 = i ∧ ij.1.2 < k then (n : ℝ) / 2 else 0 := by
  rw [partialCorrelationCholeskyEntryResidualPower]

@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_apply (i k : Fin p) (n : ℕ)
    (hki : k < i) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ⟨(i, k), hki⟩ = n := by
  simp [partialCorrelationCholeskyEntryCoordinatePower_def]

@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_apply_of_ne (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (hij : ij.1 ≠ (i, k)) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij = 0 := by
  simp [partialCorrelationCholeskyEntryCoordinatePower_def, hij]

@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_of_eq_of_lt (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (hi : ij.1.1 = i) (hk : ij.1.2 < k) :
    partialCorrelationCholeskyEntryResidualPower i k n ij = (n : ℝ) / 2 := by
  simp [partialCorrelationCholeskyEntryResidualPower_def, hi, hk]

@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_of_not (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (h : ¬(ij.1.1 = i ∧ ij.1.2 < k)) :
    partialCorrelationCholeskyEntryResidualPower i k n ij = 0 := by
  simp [partialCorrelationCholeskyEntryResidualPower_def, h]

/-- A zeroth power contributes no residual exponent. -/
@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_zero (i k : Fin p)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryResidualPower i k 0 ij = 0 := by
  simp [partialCorrelationCholeskyEntryResidualPower_def]

/-- Residual powers contributed by Cholesky entries are nonnegative. -/
theorem partialCorrelationCholeskyEntryResidualPower_nonneg (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    0 ≤ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  rw [partialCorrelationCholeskyEntryResidualPower_def]
  split_ifs
  · positivity
  · exact le_rfl

/-- The total natural coordinate power in a monomial of Cholesky entries. -/
def partialCorrelationCholeskyMonomialCoordinatePower
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) : ℕ :=
  ∑ q, partialCorrelationCholeskyEntryCoordinatePower q.1 q.2 (m q) ij

/-- The defining sum for the coordinate power in a Cholesky monomial. -/
theorem partialCorrelationCholeskyMonomialCoordinatePower_def
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialCoordinatePower m ij =
      ∑ q, partialCorrelationCholeskyEntryCoordinatePower q.1 q.2 (m q) ij := by
  rw [partialCorrelationCholeskyMonomialCoordinatePower]

/-- The coordinate exponents of a singleton monomial are the exponents of its one entry. -/
@[simp]
theorem partialCorrelationCholeskyMonomialCoordinatePower_single
    (i k : Fin p) (n : ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialCoordinatePower (Pi.single (i, k) n) ij =
      partialCorrelationCholeskyEntryCoordinatePower i k n ij := by
  classical
  rw [partialCorrelationCholeskyMonomialCoordinatePower_def]
  simp [Pi.single_apply, partialCorrelationCholeskyEntryCoordinatePower_def]

/-- The total residual power in a monomial of Cholesky entries. -/
def partialCorrelationCholeskyMonomialResidualPower
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) : ℝ :=
  ∑ q, partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij

/-- The defining sum for the residual power in a Cholesky monomial. -/
theorem partialCorrelationCholeskyMonomialResidualPower_def
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower m ij =
      ∑ q, partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij := by
  rw [partialCorrelationCholeskyMonomialResidualPower]

/-- The residual exponents of a singleton monomial are the exponents of its one entry. -/
@[simp]
theorem partialCorrelationCholeskyMonomialResidualPower_single
    (i k : Fin p) (n : ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower (Pi.single (i, k) n) ij =
      partialCorrelationCholeskyEntryResidualPower i k n ij := by
  classical
  rw [partialCorrelationCholeskyMonomialResidualPower_def]
  conv_rhs =>
    rw [← Pi.single_eq_same (M := fun _ : Fin p × Fin p ↦ ℕ) (i, k) n]
  apply Fintype.sum_eq_single (i, k)
  intro q hq
  rw [Pi.single_eq_of_ne hq]
  exact partialCorrelationCholeskyEntryResidualPower_zero q.1 q.2 ij

/-- Residual powers in Cholesky monomials are nonnegative. -/
theorem partialCorrelationCholeskyMonomialResidualPower_nonneg
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    0 ≤ partialCorrelationCholeskyMonomialResidualPower m ij := by
  rw [partialCorrelationCholeskyMonomialResidualPower_def]
  exact Finset.sum_nonneg fun q _ ↦
    partialCorrelationCholeskyEntryResidualPower_nonneg q.1 q.2 (m q) ij

private theorem pow_partialCorrelationCholeskyEntryFactor
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| ≤ 1) (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryFactor i k ij (z ij) ^ n =
      z ij ^ partialCorrelationCholeskyEntryCoordinatePower i k n ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  have hbase : 0 ≤ 1 - z ij ^ 2 :=
    sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 (hz ij))
  by_cases hc : ij.1.1 = i ∧ ij.1.2 = k
  · have hpair : ij.1 = (i, k) := Prod.ext hc.1 hc.2
    have hr : ¬(ij.1.1 = i ∧ ij.1.2 < k) := fun h ↦ (ne_of_lt h.2) hc.2
    simp only [partialCorrelationCholeskyEntryFactor_of_coordinate i k ij (z ij) hc,
      partialCorrelationCholeskyEntryCoordinatePower_def, ite_eq_left hpair,
      partialCorrelationCholeskyEntryResidualPower_def, ite_eq_right hr, Real.rpow_zero, mul_one]
  · have hpair : ij.1 ≠ (i, k) := fun h ↦ hc ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    by_cases hr : ij.1.1 = i ∧ ij.1.2 < k
    · have hsqrt : Real.sqrt (1 - z ij ^ 2) ^ n =
          (1 - z ij ^ 2) ^ ((n : ℝ) / 2) := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_div_two_eq_sqrt (n : ℝ) hbase).symm
      simp only [partialCorrelationCholeskyEntryFactor_of_residual i k ij (z ij) hr, hsqrt,
        partialCorrelationCholeskyEntryCoordinatePower_def, ite_eq_right hpair, pow_zero,
        partialCorrelationCholeskyEntryResidualPower_def, ite_eq_left hr, one_mul]
    · simp only [partialCorrelationCholeskyEntryFactor_of_other i k ij (z ij) hc hr, one_pow,
        partialCorrelationCholeskyEntryCoordinatePower_def, ite_eq_right hpair, pow_zero,
        partialCorrelationCholeskyEntryResidualPower_def, ite_eq_right hr, Real.rpow_zero, one_mul]

/-- On the closed partial-correlation cube, a natural power of a lower-triangular Cholesky entry
factors into coordinate and residual powers. -/
theorem pow_partialCorrelationCholesky_eq_prod
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| ≤ 1) (i k : Fin p) (n : ℕ)
    (hki : k ≤ i) :
    partialCorrelationCholesky z i k ^ n =
      ∏ ij, z ij ^ partialCorrelationCholeskyEntryCoordinatePower i k n ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  rw [← prod_partialCorrelationCholeskyEntryFactor z i k hki, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun ij _ ↦
    pow_partialCorrelationCholeskyEntryFactor hz i k n ij

/-- On the closed partial-correlation cube, a joint monomial in lower-triangular Cholesky entries
factors coordinatewise. -/
theorem prod_pow_partialCorrelationCholesky_eq_prod
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| ≤ 1)
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
        (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 (hz ij)))
        (fun q _ ↦ partialCorrelationCholeskyEntryResidualPower_nonneg
          q.1 q.2 (m q) ij)).symm

end TauCeti.Probability
