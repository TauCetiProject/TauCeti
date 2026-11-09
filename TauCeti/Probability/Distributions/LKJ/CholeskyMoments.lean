/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
public import TauCeti.Probability.Distributions.Beta.Symmetric

/-!
# Moments of partial-correlation Cholesky factors

The Cholesky factor built from independent centered symmetric Beta partial correlations has
explicit natural moments entry by entry.  An entry below the diagonal contributes one power of
its partial correlation and one square-root residual factor for every preceding column; a
diagonal entry has only the residual factors.  Independence therefore evaluates every natural
moment as a finite product of Beta quotients.  Entries above the diagonal are identically zero.

These formulas are the one-entry building blocks for mixed moments of LKJ correlation matrices:
after expanding `R = L Lᵀ`, each summand is a product of powers of Cholesky entries.

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
entry.  It is `n` at the coordinate indexing that entry and zero elsewhere. -/
def partialCorrelationCholeskyEntryCoordinatePower (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) : ℕ :=
  if ij.1 = (i, k) then n else 0

/-- The residual power contributed by a natural power of one Cholesky entry.  Every partial
correlation in the same row and a preceding column contributes `(1 - z²) ^ (n / 2)`. -/
def partialCorrelationCholeskyEntryResidualPower (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) : ℝ :=
  if ij.1.1 = i ∧ ij.1.2 < k then (n : ℝ) / 2 else 0

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
theorem partialCorrelationCholeskyEntryResidualPower_of_mem (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (hi : ij.1.1 = i) (hk : ij.1.2 < k) :
    partialCorrelationCholeskyEntryResidualPower i k n ij = (n : ℝ) / 2 := by
  simp [partialCorrelationCholeskyEntryResidualPower, hi, hk]

@[simp]
theorem partialCorrelationCholeskyEntryResidualPower_of_not_mem (i k : Fin p) (n : ℕ)
    (ij : strictLowerTriangle p) (h : ¬(ij.1.1 = i ∧ ij.1.2 < k)) :
    partialCorrelationCholeskyEntryResidualPower i k n ij = 0 := by
  simp [partialCorrelationCholeskyEntryResidualPower, h]

private theorem residualPower_nonneg (i k : Fin p) (n : ℕ) (ij : strictLowerTriangle p) :
    0 ≤ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  unfold partialCorrelationCholeskyEntryResidualPower
  split_ifs
  · positivity
  · exact le_rfl

private theorem ae_pow_partialCorrelationCholesky_eq_prod
    {a : strictLowerTriangle p → ℝ} (ha : ∀ ij, 0 < a ij) (i k : Fin p) (n : ℕ)
    (hki : k ≤ i) :
    (fun z ↦ partialCorrelationCholesky z i k ^ n) =ᵐ[
      Measure.pi fun ij ↦ (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)]
      fun z ↦ ∏ ij, z ij ^ partialCorrelationCholeskyEntryCoordinatePower i k n ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower i k n ij := by
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure ha] with z hz
  have hres (ij : strictLowerTriangle p) : 0 < 1 - z ij ^ 2 :=
    sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))
  rcases hki.eq_or_lt with rfl | hki
  · rw [partialCorrelationCholesky_apply_self, ← Finset.prod_pow]
    calc
      (∏ ij with ij.1.1 = k, Real.sqrt (1 - z ij ^ 2) ^ n) =
          ∏ ij with ij.1.1 = k,
            z ij ^ partialCorrelationCholeskyEntryCoordinatePower k k n ij *
              (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower k k n ij := by
        apply Finset.prod_congr rfl
        intro ij hij
        have hi : ij.1.1 = k := (Finset.mem_filter.mp hij).2
        have hik : ij.1.2 < k := hi ▸ ij.2
        have hpair : ij.1 ≠ (k, k) := fun h ↦ (ne_of_lt hik) (congrArg Prod.snd h)
        simp only [partialCorrelationCholeskyEntryCoordinatePower,
          partialCorrelationCholeskyEntryResidualPower, hpair, hi, hik, and_self, ↓reduceIte,
          pow_zero, one_mul]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (hres ij).le]
        congr 1
        ring
      _ = ∏ ij,
          z ij ^ partialCorrelationCholeskyEntryCoordinatePower k k n ij *
            (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower k k n ij := by
        apply Finset.prod_subset (Finset.filter_subset _ _)
        intro ij _ hij
        have hi : ij.1.1 ≠ k := by simpa using hij
        have hpair : ij.1 ≠ (k, k) := fun h ↦ hi (congrArg Prod.fst h)
        simp [partialCorrelationCholeskyEntryCoordinatePower,
          partialCorrelationCholeskyEntryResidualPower, hi, hpair]
  · rw [partialCorrelationCholesky_apply_of_gt z hki, mul_pow, ← Finset.prod_pow]
    let target : strictLowerTriangle p := ⟨(i, k), hki⟩
    let s := Finset.univ.filter fun ij : strictLowerTriangle p ↦
      ij.1.1 = i ∧ ij.1.2 < k
    let f := fun ij : strictLowerTriangle p ↦
      z ij ^ partialCorrelationCholeskyEntryCoordinatePower i k n ij *
        (1 - z ij ^ 2) ^ partialCorrelationCholeskyEntryResidualPower i k n ij
    have htarget : target ∉ s := by simp [target, s]
    calc
      z target ^ n * ∏ ij ∈ s, Real.sqrt (1 - z ij ^ 2) ^ n =
          f target * ∏ ij ∈ s, f ij := by
        congr 1
        · simp [f, target, partialCorrelationCholeskyEntryCoordinatePower,
            partialCorrelationCholeskyEntryResidualPower]
        · apply Finset.prod_congr rfl
          intro ij hij
          have hr : ij.1.1 = i ∧ ij.1.2 < k := (Finset.mem_filter.mp hij).2
          have hpair : ij.1 ≠ (i, k) := fun h ↦
            (ne_of_lt hr.2) (congrArg Prod.snd h)
          simp only [f, partialCorrelationCholeskyEntryCoordinatePower,
            partialCorrelationCholeskyEntryResidualPower, hpair, hr, and_self,
            ↓reduceIte, pow_zero, one_mul]
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (hres ij).le]
          congr 1
          ring
      _ = ∏ ij ∈ insert target s, f ij := (Finset.prod_insert htarget).symm
      _ = ∏ ij, f ij := by
        apply Finset.prod_subset (by simp [s])
        intro ij _ hij
        have ht : ij ≠ target := fun h ↦ hij (by simp [h])
        have hr : ¬(ij.1.1 = i ∧ ij.1.2 < k) := fun h ↦ hij (by simp [s, h])
        have hpair : ij.1 ≠ (i, k) := fun h ↦ ht (Subtype.ext h)
        simp [f, partialCorrelationCholeskyEntryCoordinatePower,
          partialCorrelationCholeskyEntryResidualPower, hpair, hr]

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
    exact add_pos_of_pos_of_nonneg (ha ij) (residualPower_nonneg i k n ij)
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
    exact add_pos_of_pos_of_nonneg (ha ij) (residualPower_nonneg i k n ij)
  · subst n
    simp
  · have hik : i < k := lt_of_not_ge hki
    simp [partialCorrelationCholesky_apply_of_lt _ hik, hn]

/-- Every natural power of an entry in the LKJ partial-correlation Cholesky construction is
integrable. -/
theorem integrable_pow_partialCorrelationCholesky_lkj (hη : 0 < η) (i k : Fin p) (n : ℕ) :
    Integrable (fun z ↦ partialCorrelationCholesky z i k ^ n)
      (Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) :=
  integrable_pow_partialCorrelationCholesky_pi_betaMeasure
    (lkjPartialCorrelationShape_pos hη) i k n

/-- The natural moments of every entry in the LKJ partial-correlation Cholesky construction are
the Beta-product moments above, with the column-dependent LKJ shapes. -/
theorem integral_pow_partialCorrelationCholesky_lkj (hη : 0 < η) (i k : Fin p) (n : ℕ) :
    ∫ z, partialCorrelationCholesky z i k ^ n
      ∂(Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)) =
      if k ≤ i then
        ∏ ij, if Even (partialCorrelationCholeskyEntryCoordinatePower i k n ij) then
          beta ((((partialCorrelationCholeskyEntryCoordinatePower i k n ij : ℕ) : ℝ) + 1) / 2)
              (lkjPartialCorrelationShape p η ij +
                partialCorrelationCholeskyEntryResidualPower i k n ij) /
            beta (1 / 2) (lkjPartialCorrelationShape p η ij)
        else 0
      else if n = 0 then 1 else 0 :=
  integral_pow_partialCorrelationCholesky_pi_betaMeasure
    (lkjPartialCorrelationShape_pos hη) i k n

end TauCeti.Probability
