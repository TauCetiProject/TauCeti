/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
import TauCeti.LinearAlgebra.Matrix.Gram

/-!
# Powers of partial-correlation Cholesky and Gram entries

On the closed partial-correlation cube, natural powers and joint monomials of lower-triangular
entries of the partial-correlation Cholesky factor split into coordinate and residual powers of
the individual partial correlations. Expanding `partialCorrelationGram z = L * Lᵀ` then expresses
every natural monomial in the correlation entries as a finite multinomial sum of products of
natural coordinate powers and nonnegative half-integer residual powers of `1 - z ij ^ 2`. This
file records these deterministic factorizations for moment calculations.
-/

public section

noncomputable section

open Real
open scoped BigOperators

namespace TauCeti

variable {p : ℕ}

/-- The contribution of one partial-correlation coordinate to a lower-triangular entry of the
triangular factor. The formula is unguarded when `k > i`. -/
def partialCorrelationCholeskyEntryFactor (i k : Fin p) (ij : strictLowerTriangle p)
    (x : ℝ) : ℝ :=
  (if ij.1.1 = i ∧ ij.1.2 = k then x else 1) *
    (if ij.1.1 = i ∧ ij.1.2 < k then Real.sqrt (1 - x ^ 2) else 1)

/-- A coordinate factor of a Cholesky entry is continuous in the partial correlation. -/
@[fun_prop]
theorem continuous_partialCorrelationCholeskyEntryFactor (i k : Fin p)
    (ij : strictLowerTriangle p) :
    Continuous (partialCorrelationCholeskyEntryFactor i k ij) := by
  unfold partialCorrelationCholeskyEntryFactor
  split_ifs <;> fun_prop

/-- The defining formula for one coordinate factor of a Cholesky entry. -/
theorem partialCorrelationCholeskyEntryFactor_def (i k : Fin p)
    (ij : strictLowerTriangle p) (x : ℝ) :
    partialCorrelationCholeskyEntryFactor i k ij x =
      (if ij.1.1 = i ∧ ij.1.2 = k then x else 1) *
        (if ij.1.1 = i ∧ ij.1.2 < k then Real.sqrt (1 - x ^ 2) else 1) := by
  rw [partialCorrelationCholeskyEntryFactor]

@[simp]
theorem partialCorrelationCholeskyEntryFactor_of_eq_of_eq (i k : Fin p)
    (ij : strictLowerTriangle p) (x : ℝ) (hi : ij.1.1 = i) (hk : ij.1.2 = k) :
    partialCorrelationCholeskyEntryFactor i k ij x = x := by
  have hr : ¬(ij.1.1 = i ∧ ij.1.2 < k) := fun h ↦ (ne_of_lt h.2) hk
  rw [partialCorrelationCholeskyEntryFactor_def, ite_eq_left ⟨hi, hk⟩,
    ite_eq_right hr, mul_one]

@[simp]
theorem partialCorrelationCholeskyEntryFactor_of_eq_of_lt (i k : Fin p)
    (ij : strictLowerTriangle p) (x : ℝ) (hi : ij.1.1 = i) (hk : ij.1.2 < k) :
    partialCorrelationCholeskyEntryFactor i k ij x = Real.sqrt (1 - x ^ 2) := by
  have hc : ¬(ij.1.1 = i ∧ ij.1.2 = k) := fun h ↦ (ne_of_lt hk) h.2
  rw [partialCorrelationCholeskyEntryFactor_def, ite_eq_right hc,
    ite_eq_left ⟨hi, hk⟩, one_mul]

@[simp]
theorem partialCorrelationCholeskyEntryFactor_self_of_eq (i : Fin p)
    (ij : strictLowerTriangle p) (x : ℝ) (hi : ij.1.1 = i) :
    partialCorrelationCholeskyEntryFactor i i ij x = Real.sqrt (1 - x ^ 2) := by
  exact partialCorrelationCholeskyEntryFactor_of_eq_of_lt i i ij x hi (hi ▸ ij.2)

@[simp]
theorem partialCorrelationCholeskyEntryFactor_of_not_of_not (i k : Fin p)
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
  · rw [partialCorrelationCholeskyEntryFactor_of_eq_of_eq i k ij x hc.1 hc.2]
    exact hx
  by_cases hr : ij.1.1 = i ∧ ij.1.2 < k
  · rw [partialCorrelationCholeskyEntryFactor_of_eq_of_lt i k ij x hr.1 hr.2,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hs'
  · rw [partialCorrelationCholeskyEntryFactor_of_not_of_not i k ij x hc hr, abs_one]

/-- A partial correlation from another row contributes the identity coordinate factor. -/
theorem partialCorrelationCholeskyEntryFactor_of_row_ne (i k : Fin p)
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

/-- The power of a partial-correlation coordinate occurring in a natural power of one
lower-triangular Cholesky entry. When `k < i`, it is `n` at `(i, k)` and zero elsewhere; when
`k = i`, it is identically zero. The formula is unguarded when `k > i`. -/
def partialCorrelationCholeskyEntryCoordinatePower (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) : ℕ :=
  if ij.1 = (i, k) then n else 0

/-- The defining formula for the coordinate power of one Cholesky entry. -/
theorem partialCorrelationCholeskyEntryCoordinatePower_def (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij =
      if ij.1 = (i, k) then n else 0 := by
  rw [partialCorrelationCholeskyEntryCoordinatePower]

/-- The residual power contributed by a natural power of one lower-triangular Cholesky entry.
Every partial correlation in the same row and a preceding column contributes
`(1 - z²) ^ (n / 2)`. The formula is unguarded when `k > i`. -/
def partialCorrelationCholeskyEntryResidualPower (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) : ℝ :=
  if ij.1.1 = i ∧ ij.1.2 < k then (n : ℝ) / 2 else 0

/-- The defining formula for the residual power of one Cholesky entry. -/
theorem partialCorrelationCholeskyEntryResidualPower_def (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryResidualPower i k n ij =
      if ij.1.1 = i ∧ ij.1.2 < k then (n : ℝ) / 2 else 0 := by
  rw [partialCorrelationCholeskyEntryResidualPower]

theorem partialCorrelationCholeskyEntryCoordinatePower_apply_self (i k : Fin p) (n : ℕ)
    (hki : k < i) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ⟨(i, k), hki⟩ = n := by
  simp [partialCorrelationCholeskyEntryCoordinatePower_def]

@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_apply_of_eq (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (hij : ij.1 = (i, k)) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij = n := by
  simp [partialCorrelationCholeskyEntryCoordinatePower_def, hij]

@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_apply_of_ne (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (hij : ij.1 ≠ (i, k)) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij = 0 := by
  simp [partialCorrelationCholeskyEntryCoordinatePower_def, hij]

/-- The coordinate exponent of one entry is the corresponding singleton function. -/
theorem partialCorrelationCholeskyEntryCoordinatePower_eq_single (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij =
      Pi.single (M := fun _ : Fin p × Fin p ↦ ℕ) (i, k) n ij.1 := by
  classical
  simp [partialCorrelationCholeskyEntryCoordinatePower_def, Pi.single_apply]

/-- A zeroth power contributes no coordinate exponent. -/
@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_zero (i k : Fin p)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryCoordinatePower i k 0 ij = 0 := by
  simp [partialCorrelationCholeskyEntryCoordinatePower_def]

/-- Diagonal and upper-triangular entries have no partial-correlation coordinate exponent. -/
@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_of_le (i k : Fin p) (n : ℕ)
    (hik : i ≤ k) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryCoordinatePower i k n ij = 0 := by
  rw [partialCorrelationCholeskyEntryCoordinatePower_def]
  split_ifs with h
  · have hki : k < i := by simpa only [h] using ij.2
    exact (not_lt_of_ge hik hki).elim
  · rfl

/-- Coordinate exponents are additive in the natural power. -/
@[simp]
theorem partialCorrelationCholeskyEntryCoordinatePower_add (i k : Fin p) (n r : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryCoordinatePower i k (n + r) ij =
      partialCorrelationCholeskyEntryCoordinatePower i k n ij +
        partialCorrelationCholeskyEntryCoordinatePower i k r ij := by
  rw [partialCorrelationCholeskyEntryCoordinatePower_def,
    partialCorrelationCholeskyEntryCoordinatePower_def,
    partialCorrelationCholeskyEntryCoordinatePower_def]
  split_ifs <;> simp

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

/-- Every coordinate preceding a diagonal entry contributes its residual exponent. -/
@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_self_of_eq (i : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (hi : ij.1.1 = i) :
    partialCorrelationCholeskyEntryResidualPower i i n ij = (n : ℝ) / 2 := by
  simp [hi, hi ▸ ij.2]

/-- A zeroth power contributes no residual exponent. -/
@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_zero (i k : Fin p)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryResidualPower i k 0 ij = 0 := by
  simp [partialCorrelationCholeskyEntryResidualPower_def]

/-- Residual exponents are additive in the natural power. -/
@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_add (i k : Fin p) (n r : ℕ)
    (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryResidualPower i k (n + r) ij =
      partialCorrelationCholeskyEntryResidualPower i k n ij +
        partialCorrelationCholeskyEntryResidualPower i k r ij := by
  rw [partialCorrelationCholeskyEntryResidualPower_def,
    partialCorrelationCholeskyEntryResidualPower_def,
    partialCorrelationCholeskyEntryResidualPower_def]
  split_ifs <;> simp [add_div]

/-- Residual powers contributed by Cholesky entries are nonnegative. -/
theorem partialCorrelationCholeskyEntryResidualPower_nonneg (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) :
    0 ≤ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  rw [partialCorrelationCholeskyEntryResidualPower_def]
  split_ifs
  · positivity
  · exact le_rfl

/-- The total residual power in a monomial supported on lower-triangular Cholesky entries. The
formula is unguarded when the monomial has support above the diagonal. -/
def partialCorrelationCholeskyMonomialResidualPower
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) : ℝ :=
  ∑ q, partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij

/-- The defining sum for the residual power in a Cholesky monomial. -/
theorem partialCorrelationCholeskyMonomialResidualPower_def
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower m ij =
      ∑ q, partialCorrelationCholeskyEntryResidualPower q.1 q.2 (m q) ij := by
  rw [partialCorrelationCholeskyMonomialResidualPower]

/-- The residual exponent at a coordinate is the half-sum of the powers of the entries to its
right in the same row. -/
theorem partialCorrelationCholeskyMonomialResidualPower_eq_sum_Ioi
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower m ij =
      ∑ k ∈ Finset.Ioi ij.1.2, (m (ij.1.1, k) : ℝ) / 2 := by
  rw [partialCorrelationCholeskyMonomialResidualPower_def, Fintype.sum_prod_type,
    Fintype.sum_eq_single ij.1.1]
  · simp only [partialCorrelationCholeskyEntryResidualPower_def, true_and]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext k
      simp
    · simp
  · intro i hi
    simp [hi.symm]

/-- The zero monomial has zero residual exponent. -/
@[simp]
theorem partialCorrelationCholeskyMonomialResidualPower_zero (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower (0 : Fin p × Fin p → ℕ) ij = 0 := by
  simp [partialCorrelationCholeskyMonomialResidualPower_def]

/-- Residual exponents are additive in the monomial multi-index. -/
@[simp]
theorem partialCorrelationCholeskyMonomialResidualPower_add
    (m n : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower (m + n) ij =
      partialCorrelationCholeskyMonomialResidualPower m ij +
        partialCorrelationCholeskyMonomialResidualPower n ij := by
  simp [partialCorrelationCholeskyMonomialResidualPower_def, Finset.sum_add_distrib]

/-- Residual exponents commute with finite sums of monomial multi-indices. -/
@[simp]
theorem partialCorrelationCholeskyMonomialResidualPower_sum {s : Type*}
    (t : Finset s) (m : s → Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower (∑ x ∈ t, m x) ij =
      ∑ x ∈ t, partialCorrelationCholeskyMonomialResidualPower (m x) ij := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert x t hxt ih => simp [hxt, ih]

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

/-- A natural power of one coordinate factor splits into its coordinate and residual powers. -/
theorem pow_partialCorrelationCholeskyEntryFactor {x : ℝ} (hx : |x| ≤ 1)
    (i k : Fin p) (n : ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyEntryFactor i k ij x ^ n =
      x ^ partialCorrelationCholeskyEntryCoordinatePower i k n ij *
        (1 - x ^ 2) ^ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  have hbase : 0 ≤ 1 - x ^ 2 :=
    sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 hx)
  by_cases hc : ij.1.1 = i ∧ ij.1.2 = k
  · have hpair : ij.1 = (i, k) := Prod.ext hc.1 hc.2
    have hr : ¬(ij.1.1 = i ∧ ij.1.2 < k) := fun h ↦ (ne_of_lt h.2) hc.2
    simp only [partialCorrelationCholeskyEntryFactor_of_eq_of_eq i k ij x hc.1 hc.2,
      partialCorrelationCholeskyEntryCoordinatePower_apply_of_eq i k n ij hpair,
      partialCorrelationCholeskyEntryResidualPower_def, ite_eq_right hr, Real.rpow_zero, mul_one]
  · have hpair : ij.1 ≠ (i, k) := fun h ↦ hc ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    by_cases hr : ij.1.1 = i ∧ ij.1.2 < k
    · have hsqrt : Real.sqrt (1 - x ^ 2) ^ n =
          (1 - x ^ 2) ^ ((n : ℝ) / 2) := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_div_two_eq_sqrt (n : ℝ) hbase).symm
      simp only [partialCorrelationCholeskyEntryFactor_of_eq_of_lt i k ij x hr.1 hr.2, hsqrt,
        partialCorrelationCholeskyEntryCoordinatePower_apply_of_ne i k n ij hpair, pow_zero,
        partialCorrelationCholeskyEntryResidualPower_def, ite_eq_left hr, one_mul]
    · simp only [partialCorrelationCholeskyEntryFactor_of_not_of_not i k ij x hc hr,
        one_pow,
        partialCorrelationCholeskyEntryCoordinatePower_apply_of_ne i k n ij hpair, pow_zero,
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
    pow_partialCorrelationCholeskyEntryFactor (hz ij) i k n ij

/-- On the closed partial-correlation cube, a joint monomial in lower-triangular Cholesky entries
factors coordinatewise. -/
theorem prod_pow_partialCorrelationCholesky_eq_prod
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| ≤ 1)
    (m : Fin p × Fin p → ℕ) (hm : ∀ q, m q ≠ 0 → q.2 ≤ q.1) :
    (∏ q, partialCorrelationCholesky z q.1 q.2 ^ m q) =
      ∏ ij, z ij ^ m ij.1 *
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
    _ = ∏ ij, z ij ^ m ij.1 *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyMonomialResidualPower m ij := by
      apply Finset.prod_congr rfl
      intro ij _
      rw [Finset.prod_mul_distrib, partialCorrelationCholeskyMonomialResidualPower_def,
        Finset.prod_pow_eq_pow_sum]
      congr 1
      · simp [partialCorrelationCholeskyEntryCoordinatePower_def]
      exact (Real.rpow_sum_of_nonneg
        (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).2 (hz ij)))
        (fun q _ ↦ partialCorrelationCholeskyEntryResidualPower_nonneg
          q.1 q.2 (m q) ij)).symm

/-- The residual exponent of a Cholesky monomial at a partial-correlation coordinate is a
nonnegative half-integer: half the sum of the natural powers of the entries strictly to its right
in the same row. -/
theorem partialCorrelationCholeskyMonomialResidualPower_eq_natCast_div_two
    (m : Fin p × Fin p → ℕ) (ij : strictLowerTriangle p) :
    partialCorrelationCholeskyMonomialResidualPower m ij =
      ((∑ k ∈ Finset.Ioi ij.1.2, m (ij.1.1, k) : ℕ) : ℝ) / 2 := by
  rw [partialCorrelationCholeskyMonomialResidualPower_eq_sum_Ioi, Nat.cast_sum, Finset.sum_div]

/-- The Cholesky-entry exponent multi-index induced by a column-split exponent family `K` in the
multinomial expansion of a `partialCorrelationGram` monomial. Entry `(i, k)` of the triangular
factor collects its occurrences as both the left and right factor in column `k`. -/
def partialCorrelationGramCholeskyPower
    (K : Fin p × Fin p → Fin p → ℕ) (q : Fin p × Fin p) : ℕ :=
  ∑ j, (K (q.1, j) q.2 + K (j, q.1) q.2)

/-- The defining row-and-column sum for the Cholesky exponent induced by `K`. -/
theorem partialCorrelationGramCholeskyPower_def
    (K : Fin p × Fin p → Fin p → ℕ) (q : Fin p × Fin p) :
    partialCorrelationGramCholeskyPower K q =
      ∑ j, (K (q.1, j) q.2 + K (j, q.1) q.2) :=
  (rfl)

/-- The zero column-split family induces the zero Cholesky multi-index. -/
@[simp]
theorem partialCorrelationGramCholeskyPower_zero (q : Fin p × Fin p) :
    partialCorrelationGramCholeskyPower (0 : Fin p × Fin p → Fin p → ℕ) q = 0 := by
  simp [partialCorrelationGramCholeskyPower_def]

/-- Induced Cholesky exponents are additive in the column-split family. -/
@[simp]
theorem partialCorrelationGramCholeskyPower_add
    (K L : Fin p × Fin p → Fin p → ℕ) (q : Fin p × Fin p) :
    partialCorrelationGramCholeskyPower (K + L) q =
      partialCorrelationGramCholeskyPower K q + partialCorrelationGramCholeskyPower L q := by
  simp only [partialCorrelationGramCholeskyPower_def, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by omega

/-- Induced Cholesky exponents commute with finite sums of column-split families. -/
@[simp]
theorem partialCorrelationGramCholeskyPower_sum {ι : Type*}
    (s : Finset ι) (K : ι → Fin p × Fin p → Fin p → ℕ) (q : Fin p × Fin p) :
    partialCorrelationGramCholeskyPower (∑ x ∈ s, K x) q =
      ∑ x ∈ s, partialCorrelationGramCholeskyPower (K x) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih => simp [hxs, ih]

/-- A column-split family supported at a single matrix entry `ab` contributes `f q.2` to row
`ab.1` and `f q.2` to row `ab.2` in column `q.2`. -/
theorem partialCorrelationGramCholeskyPower_single
    (ab : Fin p × Fin p) (f : Fin p → ℕ) (q : Fin p × Fin p) :
    partialCorrelationGramCholeskyPower (Pi.single ab f) q =
      (if ab.1 = q.1 then f q.2 else 0) + (if ab.2 = q.1 then f q.2 else 0) := by
  rw [partialCorrelationGramCholeskyPower_def, Finset.sum_add_distrib]
  congr 1
  · by_cases h1 : ab.1 = q.1
    · rw [ite_eq_left h1, Fintype.sum_eq_single ab.2]
      · rw [← Prod.eta ab, h1, Pi.single_eq_same]
      · intro j hj
        have hne : (q.1, j) ≠ ab := fun h ↦ hj (congrArg Prod.snd h)
        simp [Pi.single_eq_of_ne hne]
    · rw [ite_eq_right h1]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hne : (q.1, j) ≠ ab := fun h ↦ h1 (congrArg Prod.fst h).symm
      simp [Pi.single_eq_of_ne hne]
  · by_cases h2 : ab.2 = q.1
    · rw [ite_eq_left h2, Fintype.sum_eq_single ab.1]
      · rw [← Prod.eta ab, h2, Pi.single_eq_same]
      · intro j hj
        have hne : (j, q.1) ≠ ab := fun h ↦ hj (congrArg Prod.fst h)
        simp [Pi.single_eq_of_ne hne]
    · rw [ite_eq_right h2]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hne : (j, q.1) ≠ ab := fun h ↦ h2 (congrArg Prod.snd h).symm
      simp [Pi.single_eq_of_ne hne]

/-- For every column-split family `K` whose entrywise sums match `n`, the total Cholesky exponent
in row `i` equals the total degree of axis `i` in `n`. -/
theorem sum_partialCorrelationGramCholeskyPower_row
    {s : Fin p × Fin p → Finset (Fin p)} {n : Fin p × Fin p → ℕ}
    {K : Fin p × Fin p → Fin p → ℕ}
    (hK : K ∈ Fintype.piFinset fun ab ↦ Finset.piAntidiag (s ab) (n ab))
    (i : Fin p) :
    ∑ k, partialCorrelationGramCholeskyPower K (i, k) =
      ∑ j, (n (i, j) + n (j, i)) := by
  simp_rw [partialCorrelationGramCholeskyPower_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hsum (ab : Fin p × Fin p) : ∑ k, K ab k = n ab := by
    obtain ⟨h1, h2⟩ := Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hK ab)
    rw [← h1]
    exact (Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦
      not_imp_comm.mp (h2 k) hk).symm
  rw [Finset.sum_add_distrib, hsum (i, j), hsum (j, i)]

/-- When each column-split vector `K ab` is supported on `Finset.Iic (min ab.1 ab.2)`, the
induced Cholesky multi-index is supported on or below the diagonal. -/
theorem partialCorrelationGramCholeskyPower_le_of_mem_piFinset
    {n : Fin p × Fin p → ℕ} {K : Fin p × Fin p → Fin p → ℕ}
    (hK : K ∈ Fintype.piFinset fun ab : Fin p × Fin p ↦
      Finset.piAntidiag (Finset.Iic (min ab.1 ab.2)) (n ab))
    {q : Fin p × Fin p} (hq : partialCorrelationGramCholeskyPower K q ≠ 0) :
    q.2 ≤ q.1 := by
  rw [partialCorrelationGramCholeskyPower_def] at hq
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  by_cases hleft : K (q.1, j) q.2 ≠ 0
  · have hmem := (Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hK (q.1, j))).2 q.2 hleft
    exact (le_min_iff.mp (Finset.mem_Iic.mp hmem)).1
  · have hright : K (j, q.1) q.2 ≠ 0 := by omega
    have hmem := (Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hK (j, q.1))).2 q.2 hright
    exact (le_min_iff.mp (Finset.mem_Iic.mp hmem)).2

/-- Every entry of the partial-correlation Gram matrix sums only over Cholesky columns at most
`min i j`. -/
theorem partialCorrelationGram_apply_eq_sum_Iic_min
    (z : strictLowerTriangle p → ℝ) (i j : Fin p) :
    partialCorrelationGram z i j =
      ∑ k ∈ Finset.Iic (min i j),
        partialCorrelationCholesky z i k * partialCorrelationCholesky z j k := by
  rw [partialCorrelationGram_def]
  exact (isLowerTriangular_partialCorrelationCholesky z).mul_transpose_apply_eq_sum_Iic i j

/-- Every natural monomial in the entries of `partialCorrelationGram z` expands as a multinomial
sum of lower-triangular monomials in `partialCorrelationCholesky z`. -/
theorem prod_pow_partialCorrelationGram_eq_sum_prod_pow_partialCorrelationCholesky
    (z : strictLowerTriangle p → ℝ) (n : Fin p × Fin p → ℕ) :
    (∏ ab, partialCorrelationGram z ab.1 ab.2 ^ n ab) =
      ∑ K ∈ Fintype.piFinset (fun ab : Fin p × Fin p ↦
          Finset.piAntidiag (Finset.Iic (min ab.1 ab.2)) (n ab)),
        (∏ ab, (Nat.multinomial Finset.univ (K ab) : ℝ)) *
          ∏ q, partialCorrelationCholesky z q.1 q.2 ^
            partialCorrelationGramCholeskyPower K q := by
  rw [partialCorrelationGram_def,
    (isLowerTriangular_partialCorrelationCholesky z).prod_pow_mul_transpose_apply n]
  simp only [partialCorrelationGramCholeskyPower_def]

/-- On the closed partial-correlation cube, every natural monomial in the entries of
`partialCorrelationGram z` expands into a finite multinomial sum of coordinatewise products of
natural partial-correlation powers and nonnegative half-integer powers of `1 - z ij ^ 2`. -/
theorem prod_pow_partialCorrelationGram_eq_sum_prod
    {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| ≤ 1)
    (n : Fin p × Fin p → ℕ) :
    (∏ ab, partialCorrelationGram z ab.1 ab.2 ^ n ab) =
      ∑ K ∈ Fintype.piFinset (fun ab : Fin p × Fin p ↦
          Finset.piAntidiag (Finset.Iic (min ab.1 ab.2)) (n ab)),
        (∏ ab, (Nat.multinomial Finset.univ (K ab) : ℝ)) *
          ∏ ij : strictLowerTriangle p,
            z ij ^ partialCorrelationGramCholeskyPower K ij.1 *
              (1 - z ij ^ 2) ^
                partialCorrelationCholeskyMonomialResidualPower
                  (partialCorrelationGramCholeskyPower K) ij := by
  rw [prod_pow_partialCorrelationGram_eq_sum_prod_pow_partialCorrelationCholesky]
  refine Finset.sum_congr rfl fun K hK ↦ ?_
  rw [prod_pow_partialCorrelationCholesky_eq_prod hz _
    fun _ ↦ partialCorrelationGramCholeskyPower_le_of_mem_piFinset hK]

end TauCeti
