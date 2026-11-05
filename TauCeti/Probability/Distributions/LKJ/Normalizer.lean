/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Correlation
import TauCeti.Probability.Distributions.Beta.Measurability

/-!
# The LKJ normalizing constant

The density of the LKJ law of shape `η` on `p × p` correlation matrices is proportional to
`det R ^ (η - 1)`.  In partial-correlation coordinates its normalizing constant is a finite
product of Euler beta functions.  This file defines that product, records its algebraic API, and
proves that it is the integral it is named for: for `0 < η`,

`∫ x in posDefCorrelationRegion p, det (correlationMatrix p x) ^ (η - 1) = lkjNormalizer p η`,

both in strictly lower correlation coordinates and against the reference measure
`TauCeti.correlationLebesgue p`.  The proof changes variables to partial correlations, where the
determinant and the Jacobian both factor into powers of the residual variances `1 - z ^ 2`, and
evaluates each coordinate by `∫ z in -1..1, (1 - z ^ 2) ^ (b - 1) = Β(1 / 2, b)`.

We index the factors by `k = p - j`, where `j` is the one-based column index in the usual
partial-correlation formula.  Thus

`lkjNormalizer p η = ∏ k ∈ Finset.Ico 1 p, beta (1 / 2) (η + (k - 1) / 2) ^ k`.

The reflected-index theorem gives the equivalent column-indexed form.  Legendre's duplication
formula also rewrites every factor as the normalizer of a symmetric beta law; this is the form
used by the independent-beta construction of LKJ partial correlations.

## Main declarations

* `TauCeti.Probability.lkjNormalizer` — the LKJ normalizing constant.
* `TauCeti.Probability.lkjNormalizer_eq_prod_columns` — the conventional one-based
  column-indexed formula.
* `TauCeti.Probability.lkjNormalizer_succ` — the recurrence in the matrix dimension.
* `TauCeti.Probability.lkjNormalizer_eq_prod_beta_self` — the symmetric-beta form of the
  product.
* `TauCeti.Probability.setIntegral_rpow_det_posDefCorrelationRegion`,
  `TauCeti.Probability.integrableOn_rpow_det_posDefCorrelationRegion` — the normalizing integral
  in correlation coordinates.
* `TauCeti.Probability.setIntegral_rpow_det_correlationLebesgue`,
  `TauCeti.Probability.integrableOn_rpow_det_correlationLebesgue` — the same integral against
  `TauCeti.correlationLebesgue p`.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace TauCeti.Probability

/-- The normalizing constant for the `p × p` LKJ correlation-matrix law of shape `η`.

The factor indexed by `k` occurs once for each of the `k` partial correlations in the
corresponding column of the triangular parametrization.  The intended parameter range is
`0 < η`; the formula is left total outside that range. -/
def lkjNormalizer (p : ℕ) (η : ℝ) : ℝ :=
  ∏ k ∈ Finset.Ico 1 p,
    ProbabilityTheory.beta (1 / 2) (η + ((k : ℝ) - 1) / 2) ^ k

/-- The defining row-indexed beta product for the LKJ normalizing constant. -/
theorem lkjNormalizer_def (p : ℕ) (η : ℝ) :
    lkjNormalizer p η =
      ∏ k ∈ Finset.Ico 1 p,
        ProbabilityTheory.beta (1 / 2) (η + ((k : ℝ) - 1) / 2) ^ k := by
  rw [lkjNormalizer]

/-- The LKJ normalizer in the conventional one-based column indexing.  The column `j` contributes
`p - j` partial correlations, each with second beta parameter
`η + (p - j - 1) / 2`. -/
theorem lkjNormalizer_eq_prod_columns (p : ℕ) (η : ℝ) :
    lkjNormalizer p η =
      ∏ j ∈ Finset.Ico 1 p,
        ProbabilityTheory.beta (1 / 2)
          (η + (((p - j : ℕ) : ℝ) - 1) / 2) ^ (p - j) := by
  simpa [lkjNormalizer] using (Finset.prod_Ico_reflect
    (fun k : ℕ ↦ ProbabilityTheory.beta (1 / 2)
      (η + ((k : ℝ) - 1) / 2) ^ k) 1 (m := p) (n := p) p.le_succ).symm

/-- In dimensions zero and one the LKJ normalizing constant is the empty product. -/
@[simp]
theorem lkjNormalizer_zero (η : ℝ) : lkjNormalizer 0 η = 1 := by
  simp [lkjNormalizer]

/-- In dimension one the LKJ normalizing constant is one. -/
@[simp]
theorem lkjNormalizer_one (η : ℝ) : lkjNormalizer 1 η = 1 := by
  simp [lkjNormalizer]

/-- In dimension two the single free correlation has beta normalizer `B(1/2, η)`. -/
@[simp]
theorem lkjNormalizer_two (η : ℝ) :
    lkjNormalizer 2 η = ProbabilityTheory.beta (1 / 2) η := by
  norm_num [lkjNormalizer]

/-- Increasing the matrix dimension appends the `k = p` product factor, corresponding after
reindexing to the first column in dimension `p + 1`. -/
theorem lkjNormalizer_succ (p : ℕ) (η : ℝ) :
    lkjNormalizer (p + 1) η = lkjNormalizer p η *
      ProbabilityTheory.beta (1 / 2) (η + ((p : ℝ) - 1) / 2) ^ p := by
  rcases p with _ | p
  · simp
  · exact Finset.prod_Ico_succ_top (Nat.succ_pos p) _

/-- Every beta parameter in the LKJ normalizer is positive when the shape is positive. -/
private theorem lkj_betaParameter_pos {η : ℝ} (hη : 0 < η) {k : ℕ}
    (hk : k ∈ Finset.Ico 1 p) :
    0 < η + ((k : ℝ) - 1) / 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
  positivity

/-- The LKJ normalizing constant is strictly positive on its parameter domain. -/
theorem lkjNormalizer_pos {p : ℕ} {η : ℝ} (hη : 0 < η) : 0 < lkjNormalizer p η := by
  rw [lkjNormalizer]
  exact Finset.prod_pos fun k hk ↦ pow_pos
    (ProbabilityTheory.beta_pos (by norm_num) (lkj_betaParameter_pos hη hk)) k

/-- The LKJ normalizing constant does not vanish on its parameter domain. -/
theorem lkjNormalizer_ne_zero {p : ℕ} {η : ℝ} (hη : 0 < η) :
    lkjNormalizer p η ≠ 0 :=
  (lkjNormalizer_pos hη).ne'

/-- The LKJ normalizer is Borel measurable as a function of its shape parameter. -/
@[fun_prop]
theorem measurable_lkjNormalizer (p : ℕ) : Measurable (lkjNormalizer p) := by
  unfold lkjNormalizer
  refine Finset.measurable_prod _ fun k _ ↦ ?_
  have hk : Measurable fun η : ℝ ↦ η + ((k : ℝ) - 1) / 2 := by fun_prop
  exact (measurable_beta.comp (measurable_const.prodMk hk)).pow_const k

/-- Legendre's duplication formula rewrites the LKJ normalizer as a product of symmetric-beta
normalizers.  This is the factorization used when partial correlations are constructed from
independent symmetric beta variables on `(0, 1)`. -/
theorem lkjNormalizer_eq_prod_beta_self {p : ℕ} {η : ℝ} (hη : 0 < η) :
    lkjNormalizer p η =
      ∏ k ∈ Finset.Ico 1 p,
        ((2 : ℝ) ^ (2 * (η + ((k : ℝ) - 1) / 2) - 1) *
          ProbabilityTheory.beta (η + ((k : ℝ) - 1) / 2)
            (η + ((k : ℝ) - 1) / 2)) ^ k := by
  rw [lkjNormalizer]
  apply Finset.prod_congr rfl
  intro k hk
  rw [ProbabilityTheory.beta_one_half_left_eq_two_rpow_mul_beta_self
    (lkj_betaParameter_pos hη hk)]

/-! ### The normalizing integral -/

variable {p : ℕ} {η : ℝ}

/-- Grouping the strictly lower positions by column: the zero-based column `j` contains
`p - 1 - j` positions. -/
private theorem prod_strictLowerTriangle_eq_prod_Ico (F : ℕ → ℝ) :
    ∏ ij : strictLowerTriangle p, F (p - ij.1.2.1 - 2) = ∏ k ∈ Finset.Ico 1 p, F (k - 1) ^ k := by
  have hcard (j : Fin p) :
      (Finset.univ.filter fun ij : strictLowerTriangle p ↦ ij.1.2 = j).card = p - 1 - j := by
    rw [← Fin.card_Ioi j]
    refine Finset.card_bij (fun ij _ ↦ ij.1.1) (fun ij hij ↦ ?_) (fun ij hij kl hkl h ↦ ?_)
      fun i hi ↦ ⟨⟨(i, j), Finset.mem_Ioi.1 hi⟩, by simp, rfl⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
      exact Finset.mem_Ioi.2 (hij ▸ ij.2)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij hkl
      exact Subtype.ext (Prod.ext h (hij.trans hkl.symm))
  calc
    _ = ∏ j : Fin p, ∏ ij : strictLowerTriangle p with ij.1.2 = j, F (p - ij.1.2.1 - 2) :=
      (Finset.prod_fiberwise _ _ _).symm
    _ = ∏ j : Fin p, F (p - 1 - j - 1) ^ (p - 1 - j) := by
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [Finset.prod_congr rfl fun ij hij ↦ by
        rw [(Finset.mem_filter.1 hij).2], Finset.prod_const, hcard]
      congr 2
      omega
    _ = ∏ k ∈ Finset.range p, F (k - 1) ^ k :=
      (Fin.prod_univ_eq_prod_range (fun j ↦ F (p - 1 - j - 1) ^ (p - 1 - j)) p).trans
        (Finset.prod_range_reflect (fun k ↦ F (k - 1) ^ k) p)
    _ = _ := by
      refine (Finset.prod_subset (fun k hk ↦ ?_) fun k hk hk' ↦ ?_).symm
      · exact Finset.mem_range.2 (Finset.mem_Ico.1 hk).2
      · obtain rfl : k = 0 := by
          simp only [Finset.mem_range, Finset.mem_Ico, not_and, not_lt] at hk hk'
          omega
        simp

/-- On the open cube the Jacobian-weighted power of the determinant factors into one-dimensional
powers of the residual variances `1 - z ij ^ 2`. -/
private theorem jacobian_mul_det_rpow {z : strictLowerTriangle p → ℝ} (hz : ∀ ij, |z ij| < 1) :
    (∏ ij : strictLowerTriangle p, Real.sqrt (1 - z ij ^ 2) ^ (p - ij.1.2.1 - 2)) •
        (correlationMatrix p (correlationCoordinatesOfPartialCorrelation z) :
          Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) =
      ∏ ij : strictLowerTriangle p,
        (1 - z ij ^ 2) ^ ((η + ((p - ij.1.2.1 - 2 : ℕ) : ℝ) / 2) - 1) := by
  have hpos (ij : strictLowerTriangle p) : 0 < 1 - z ij ^ 2 :=
    sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 (hz ij))
  rw [coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation fun ij ↦ (hz ij).le,
    det_partialCorrelationGram fun ij ↦ (hz ij).le,
    ← Real.finsetProd_rpow _ _ (fun ij _ ↦ (hpos ij).le), smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ij _ ↦ ?_
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (hpos ij).le,
    ← Real.rpow_add (hpos ij)]
  congr 1
  ring

/-- The open partial-correlation cube as a product of open intervals. -/
private theorem partialCorrelationCube_eq_pi :
    {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} = univ.pi fun _ ↦ Ioo (-1) 1 := by
  ext z
  simp [abs_lt]

private theorem measurableSet_partialCorrelationCube :
    MeasurableSet {z : strictLowerTriangle p → ℝ | ∀ ij, |z ij| < 1} := by
  rw [partialCorrelationCube_eq_pi]
  exact .univ_pi fun _ ↦ measurableSet_Ioo

variable (p) in
/-- For positive shape `η`, the power `det R ^ (η - 1)` of the determinant of a correlation
matrix is integrable over the positive-definite correlation region. -/
theorem integrableOn_rpow_det_posDefCorrelationRegion (hη : 0 < η) :
    IntegrableOn (fun x ↦ (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1))
      (posDefCorrelationRegion p) := by
  rw [← integrableOn_comp_correlationCoordinatesOfPartialCorrelation_iff,
    integrableOn_congr_fun (fun z hz ↦ jacobian_mul_det_rpow hz)
      measurableSet_partialCorrelationCube,
    partialCorrelationCube_eq_pi, IntegrableOn, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (f := fun (ij : strictLowerTriangle p) (t : ℝ) ↦
      (1 - t ^ 2) ^ ((η + ((p - ij.1.2.1 - 2 : ℕ) : ℝ) / 2) - 1)) fun _ ↦
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1
      (intervalIntegrable_one_sub_sq_rpow (by positivity))

variable (p) in
/-- **The LKJ normalizing constant as an integral.** For positive shape `η`, the integral of
`det R ^ (η - 1)` over the coordinates of the positive-definite correlation matrices is
`lkjNormalizer p η`. -/
theorem setIntegral_rpow_det_posDefCorrelationRegion (hη : 0 < η) :
    ∫ x in posDefCorrelationRegion p,
        (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) =
      lkjNormalizer p η := by
  rw [← setIntegral_comp_correlationCoordinatesOfPartialCorrelation,
    setIntegral_congr_fun measurableSet_partialCorrelationCube
      fun z hz ↦ jacobian_mul_det_rpow hz,
    partialCorrelationCube_eq_pi, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (ij : strictLowerTriangle p) (t : ℝ) ↦
      (1 - t ^ 2) ^ ((η + ((p - ij.1.2.1 - 2 : ℕ) : ℝ) / 2) - 1))]
  have h1 (ij : strictLowerTriangle p) :
      ∫ t in Ioo (-1 : ℝ) 1, (1 - t ^ 2) ^ ((η + ((p - ij.1.2.1 - 2 : ℕ) : ℝ) / 2) - 1) =
        beta (1 / 2) (η + ((p - ij.1.2.1 - 2 : ℕ) : ℝ) / 2) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      integral_one_sub_sq_rpow (by positivity)]
  simp_rw [h1]
  rw [prod_strictLowerTriangle_eq_prod_Ico (fun m ↦ beta (1 / 2) (η + (m : ℝ) / 2)),
    lkjNormalizer]
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [Nat.cast_sub (Finset.mem_Ico.1 hk).1, Nat.cast_one]

variable (p) in
/-- For positive shape `η`, the power `det R ^ (η - 1)` is integrable over the positive-definite
correlation matrices with respect to the reference measure `TauCeti.correlationLebesgue p`. -/
theorem integrableOn_rpow_det_correlationLebesgue (hη : 0 < η) :
    IntegrableOn (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1))
      {R | (R : Matrix (Fin p) (Fin p) ℝ).PosDef} (correlationLebesgue p) :=
  ((measurePreserving_correlationMatrix p).integrableOn_comp_preimage
    (measurableEmbedding_correlationMatrix p)).1 <| by
      rw [preimage_correlationMatrix_setOf_posDef]
      exact integrableOn_rpow_det_posDefCorrelationRegion p hη

variable (p) in
/-- For positive shape `η`, the integral of `det R ^ (η - 1)` over the positive-definite
correlation matrices with respect to `TauCeti.correlationLebesgue p` is `lkjNormalizer p η`. -/
theorem setIntegral_rpow_det_correlationLebesgue (hη : 0 < η) :
    ∫ R in {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (R : Matrix (Fin p) (Fin p) ℝ).PosDef},
      (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) ∂correlationLebesgue p = lkjNormalizer p η := by
  rw [← (measurePreserving_correlationMatrix p).setIntegral_preimage_emb
    (measurableEmbedding_correlationMatrix p), preimage_correlationMatrix_setOf_posDef]
  exact setIntegral_rpow_det_posDefCorrelationRegion p hη

end TauCeti.Probability
