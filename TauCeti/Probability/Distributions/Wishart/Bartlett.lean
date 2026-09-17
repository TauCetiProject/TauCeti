/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky
public import TauCeti.Probability.Distributions.Wishart.Nonsingular
public import Mathlib.Probability.Distributions.Gaussian.Real

import TauCeti.LinearAlgebra.Matrix.Cholesky.Coordinates
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.Probability.Distributions.Gamma.Sqrt
import Mathlib.Algebra.Order.Star.Real

/-!
# The standard Wishart density in Cholesky coordinates

A positive-definite symmetric `p × p` matrix `A` is `L * Lᵀ` for a unique lower-triangular `L`
with positive diagonal. This file shows that the standard Wishart density of real degree `n`,

`(det A) ^ ((n - p - 1) / 2) * exp (-trace A / 2) / (2 ^ (n * p / 2) * Γ_p (n / 2))`

against `TauCeti.symmetricLebesgue p` on the positive-definite cone, becomes a product density in
the entries of `L`. Precisely, assume `(p : ℝ) - 1 < n`, so that every `n - i` with `i < p` is
positive, and take independent real coordinates indexed by the on-or-below diagonal positions
`(i, j)`, `j ≤ i`, of a `p × p` matrix, where

* the diagonal coordinate `(i, i)` has the chi density with `n - i` degrees of freedom,
  `2 ^ (1 - k / 2) / Γ (k / 2) * t ^ (k - 1) * exp (-t ^ 2 / 2)` on `t > 0` with `k = n - i`,
  and
* a strictly lower coordinate has the standard Gaussian law `gaussianReal 0 1`.

Then the random symmetric matrix `L * Lᵀ` built from these coordinates has the standard Wishart
density. Since `L ↦ L * Lᵀ` is the inverse of the Cholesky factorization on the positive-definite
cone, this is the input from which the Bartlett decomposition of a standard Wishart matrix into
independent chi-distributed diagonal and standard Gaussian strictly lower Cholesky entries is
read off.

In the coordinates of `L` the determinant of `L * Lᵀ` is the square of the product of the
diagonal entries and its trace is the sum of the squares of all entries, so, multiplied by the
Jacobian `2 ^ p * ∏ i, (L i i) ^ (p - i)` of the Cholesky change of variables
`TauCeti.map_cholesky_symmetricLebesgue`, the Wishart density becomes one factor per coordinate.

## Main declarations

* `TauCeti.bartlettCoordinateMeasure` — the coordinate measure of one Cholesky coordinate; for
  `(p : ℝ) - 1 < n` it is the chi or standard Gaussian law of that coordinate.
* `TauCeti.map_lowerTriangleGram_pi_bartlettCoordinateMeasure` — the Gram matrix of independent
  coordinates with these laws has the standard Wishart density, and
  `TauCeti.nonsingularWishartMeasure_one_eq_map_lowerTriangleGram` records that density as the
  named law `TauCeti.nonsingularWishartMeasure n 1`.
* `TauCeti.isProbabilityMeasure_bartlettCoordinateMeasure` — each coordinate law is a probability
  measure in the degree range where the diagonal degrees of freedom are positive, and
  `TauCeti.ae_mem_posDiagLowerRegion_pi_bartlettCoordinateMeasure` — the coordinates almost surely
  have positive diagonal.

## References

* M. S. Bartlett, *On the theory of statistical regression*, Proc. Roy. Soc. Edinburgh 53 (1933),
  260–283.
* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Section 3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal Matrix

namespace TauCeti

variable {p : ℕ} {n : ℝ}

/-- The coordinate measure at the on-or-below-diagonal position `ij` of the Cholesky factor of a
standard Wishart matrix of real degree `n`. At a diagonal position `(i, i)` it is Lebesgue measure
on the positive half-line with the chi density formula for `n - i` degrees of freedom, and at a
strictly lower position it is the standard Gaussian law. The definition places no condition on
`n`: the diagonal measure is the chi probability law only when `0 < n - i`, which holds for every
`i < p` under the nonzero-dimensional hypothesis `(p : ℝ) - 1 < n` of
`TauCeti.map_lowerTriangleGram_pi_bartlettCoordinateMeasure`. -/
def bartlettCoordinateMeasure (n : ℝ) (ij : lowerTriangle p) : Measure ℝ :=
  if ij.1.1 = ij.1.2 then
    (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
      ((2 : ℝ) ^ (1 - (n - ij.1.1) / 2) / Real.Gamma ((n - ij.1.1) / 2) *
        t ^ (n - ij.1.1 - 1) * exp (-t ^ 2 / 2))
  else gaussianReal 0 1

/-- At a diagonal position `(i, i)` the coordinate measure is Lebesgue measure on the positive
half-line with the chi density formula for `n - i` degrees of freedom; it is the chi law when
`0 < n - i`. -/
@[simp]
theorem bartlettCoordinateMeasure_of_eq (n : ℝ) {ij : lowerTriangle p} (h : ij.1.1 = ij.1.2) :
    bartlettCoordinateMeasure n ij =
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
        ((2 : ℝ) ^ (1 - (n - ij.1.1) / 2) / Real.Gamma ((n - ij.1.1) / 2) *
          t ^ (n - ij.1.1 - 1) * exp (-t ^ 2 / 2)) :=
  ite_eq_left_iff.2 fun h' ↦ absurd h h'

/-- A strictly lower Cholesky coordinate is standard Gaussian. -/
@[simp]
theorem bartlettCoordinateMeasure_of_ne (n : ℝ) {ij : lowerTriangle p} (h : ij.1.1 ≠ ij.1.2) :
    bartlettCoordinateMeasure n ij = gaussianReal 0 1 :=
  ite_eq_right_iff.2 fun h' ↦ absurd h' h

/-- The real density of `TauCeti.bartlettCoordinateMeasure n ij` against Lebesgue measure. -/
private def bartlettCoordinatePDFReal (n : ℝ) (ij : lowerTriangle p) (t : ℝ) : ℝ :=
  if ij.1.1 = ij.1.2 then
    (Ioi (0 : ℝ)).indicator (fun t ↦ (2 : ℝ) ^ (1 - (n - ij.1.1) / 2) /
      Real.Gamma ((n - ij.1.1) / 2) * t ^ (n - ij.1.1 - 1) * exp (-t ^ 2 / 2)) t
  else gaussianPDFReal 0 1 t

private theorem measurable_bartlettCoordinatePDFReal (n : ℝ) (ij : lowerTriangle p) :
    Measurable (bartlettCoordinatePDFReal n ij) := by
  unfold bartlettCoordinatePDFReal
  split_ifs
  · exact (Measurable.indicator (by fun_prop) measurableSet_Ioi)
  · exact measurable_gaussianPDFReal 0 1

private theorem bartlettCoordinateMeasure_eq_withDensity (n : ℝ) (ij : lowerTriangle p) :
    bartlettCoordinateMeasure n ij =
      volume.withDensity fun t ↦ ENNReal.ofReal (bartlettCoordinatePDFReal n ij t) := by
  unfold bartlettCoordinateMeasure bartlettCoordinatePDFReal
  split_ifs
  · rw [← withDensity_indicator measurableSet_Ioi]
    congr 1
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht]
  · rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, gaussianPDF_def]

/-- Every Bartlett coordinate measure is sigma-finite, enabling their product over the
lower-triangular coordinates to be formed with `Measure.pi`. -/
instance (n : ℝ) (ij : lowerTriangle p) : SigmaFinite (bartlettCoordinateMeasure n ij) := by
  rw [bartlettCoordinateMeasure_eq_withDensity]
  infer_instance

/-- One row of constants: the chi normalizer of the diagonal coordinate `(i, i)` together with the
`i` Gaussian normalizers of the strictly lower coordinates of row `i`. -/
private theorem bartlett_row_const (n : ℝ) (i : ℕ) :
    (2 : ℝ) ^ (1 - (n - i) / 2) / Real.Gamma ((n - i) / 2) * (√(2 * π))⁻¹ ^ i =
      2 / (2 ^ (n / 2) * π ^ ((i : ℝ) / 2) * Real.Gamma (n / 2 - (i : ℝ) / 2)) := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have hsqrt : √(2 * π) ^ i = 2 ^ ((i : ℝ) / 2) * π ^ ((i : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.mul_rpow h2.le pi_pos.le]
    ring_nf
  have hexp : (1 : ℝ) - (n - i) / 2 = 1 + (i : ℝ) / 2 - n / 2 := by ring
  have hpow : (2 : ℝ) ^ (1 - (n - i) / 2) = 2 * 2 ^ ((i : ℝ) / 2) / 2 ^ (n / 2) := by
    rw [hexp, Real.rpow_sub h2, Real.rpow_add h2, Real.rpow_one]
  rw [inv_pow, hsqrt, hpow, sub_div n (i : ℝ) 2]
  have : (0 : ℝ) < 2 ^ ((i : ℝ) / 2) := by positivity
  have : (0 : ℝ) < π ^ ((i : ℝ) / 2) := by positivity
  have : (0 : ℝ) < 2 ^ (n / 2) := by positivity
  rcases eq_or_ne (Real.Gamma (n / 2 - (i : ℝ) / 2)) 0 with hΓ | hΓ
  · simp [hΓ]
  · field_simp

/-- On the positive-diagonal region the product of the coordinate densities is the standard
Wishart density of `L * Lᵀ` times the Cholesky Jacobian. -/
private theorem prod_bartlettCoordinatePDFReal {x : lowerTriangle p → ℝ}
    (hx : x ∈ posDiagLowerRegion p) :
    ∏ ij, bartlettCoordinatePDFReal n ij (x ij) =
      (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - i.1)) *
        ((lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ ((n - p - 1) / 2) *
          exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace / 2) /
            (2 ^ (n * p / 2) * multivariateGamma p (n / 2))) := by
  classical
  have hpos : ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩ := (mem_posDiagLowerRegion p).1 hx
  -- Each coordinate density is a row-dependent constant times a Gaussian factor.
  have hfac : ∀ ij : lowerTriangle p, bartlettCoordinatePDFReal n ij (x ij) =
      (if ij.1.1 = ij.1.2 then
          (2 : ℝ) ^ (1 - (n - ij.1.1) / 2) / Real.Gamma ((n - ij.1.1) / 2) *
            x ⟨(ij.1.1, ij.1.1), le_rfl⟩ ^ (n - ij.1.1 - 1)
        else (√(2 * π))⁻¹) * exp (-x ij ^ 2 / 2) := by
    intro ij
    simp only [bartlettCoordinatePDFReal]
    split_ifs with h
    · have hij : ij = ⟨(ij.1.1, ij.1.1), le_rfl⟩ := Subtype.ext (Prod.ext rfl h.symm)
      rw [Set.indicator_of_mem (by rw [hij]; exact hpos ij.1.1), ← hij]
    · simp [gaussianPDFReal_def]
  have htwo : (2 : ℝ) ^ (n * p / 2) = ∏ _i : Fin p, (2 : ℝ) ^ (n / 2) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul two_pos.le]
    ring_nf
  have hconst :
      (∏ i : Fin p,
          ((2 : ℝ) ^ (1 - (n - i.1) / 2) / Real.Gamma ((n - i.1) / 2)) *
            (√(2 * π))⁻¹ ^ i.1) =
        2 ^ p / (2 ^ (n * p / 2) * multivariateGamma p (n / 2)) := by
    rw [Finset.prod_congr rfl fun i _ ↦ by simpa using bartlett_row_const n i.1]
    simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    have htwo' : ((2 : ℝ) ^ (n / 2)) ^ p = 2 ^ (n * p / 2) := by
      simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using htwo.symm
    rw [htwo', multivariateGamma_eq_prod, Finset.prod_mul_distrib]
    ring
  have hcore := prod_lowerTriangle_diag_rpow_mul_exp_neg_sq x hpos ((n - p - 1) / 2)
    (1 / 2) (fun i ↦ (2 : ℝ) ^ (1 - (n - i.1) / 2) /
      Real.Gamma ((n - i.1) / 2)) (√(2 * π))⁻¹
  have hexponent : ∀ i : Fin p,
      2 * ((n - p - 1) / 2) + p - ((i : ℕ) : ℝ) = n - i.1 - 1 := by
    intro i
    ring
  have hexp (t : ℝ) : -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 := by ring
  have htrace : -(1 / 2 : ℝ) *
      (lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace =
        -(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace / 2 := by ring
  simp_rw [hexponent, hexp] at hcore
  rw [htrace] at hcore
  rw [Finset.prod_congr rfl fun ij _ ↦ hfac ij, hcore, hconst]
  ring

/-- For `(p : ℝ) - 1 < n` every chi coordinate has positive degrees of freedom, so the coordinate
densities are nonnegative. -/
private theorem bartlettCoordinatePDFReal_nonneg (hn : (p : ℝ) - 1 < n) (ij : lowerTriangle p)
    (t : ℝ) : 0 ≤ bartlettCoordinatePDFReal n ij t := by
  unfold bartlettCoordinatePDFReal
  split_ifs
  · refine Set.indicator_nonneg (fun t (ht : 0 < t) ↦ ?_) t
    have hi : ((ij.1.1 : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast ij.1.1.2
    have hk : 0 < (n - ij.1.1) / 2 := by linarith
    have := Real.Gamma_pos_of_pos hk
    positivity
  · exact (gaussianPDFReal_pos 0 1 t one_ne_zero).le

/-- A coordinate vector off the positive-diagonal region has a nonpositive diagonal coordinate,
where the chi density vanishes. -/
private theorem prod_bartlettCoordinatePDFReal_of_notMem {x : lowerTriangle p → ℝ}
    (hx : x ∉ posDiagLowerRegion p) : ∏ ij, bartlettCoordinatePDFReal n ij (x ij) = 0 := by
  obtain ⟨i, hi⟩ := not_forall.1 ((mem_posDiagLowerRegion p).not.1 hx)
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨(i, i), le_rfl⟩ : lowerTriangle p)) ?_
  have hmem : x (⟨(i, i), le_rfl⟩ : lowerTriangle p) ∉ Ioi (0 : ℝ) := by simpa using hi
  simp [bartlettCoordinatePDFReal, Set.indicator_of_notMem hmem]

/-- **The standard Wishart law in Cholesky coordinates.** Let the on-or-below-diagonal entries of
a lower-triangular `p × p` matrix `L` be independent, the diagonal entry `L i i` with the chi
density with `n - i` degrees of freedom and each strictly lower entry standard Gaussian. If `p = 0`,
the equality below holds for every `n`; otherwise assume `(p : ℝ) - 1 < n`. Then the symmetric
matrix `L * Lᵀ` has the standard Wishart density of degree `n`,
`(det A) ^ ((n - p - 1) / 2) * exp (-trace A / 2) / (2 ^ (n * p / 2) * Γ_p (n / 2))` on the
positive-definite cone, against `TauCeti.symmetricLebesgue p`. -/
theorem map_lowerTriangleGram_pi_bartlettCoordinateMeasure
    (hn : p = 0 ∨ (p : ℝ) - 1 < n) :
    (Measure.pi (bartlettCoordinateMeasure (p := p) n)).map (lowerTriangleGram p) =
      ((symmetricLebesgue p).restrict
          {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
            (A : Matrix (Fin p) (Fin p) ℝ).PosDef}).withDensity fun A ↦
        ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n - p - 1) / 2) *
          exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace / 2) /
            (2 ^ (n * p / 2) * multivariateGamma p (n / 2))) := by
  rcases hn with rfl | hn
  · rw [Measure.pi_of_empty _ 0, Measure.map_dirac, symmetricLebesgue_zero]
    have hgram : lowerTriangleGram 0 (0 : lowerTriangle 0 → ℝ) = 0 := Subsingleton.elim _ _
    have hcone : {A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) |
        (A : Matrix (Fin 0) (Fin 0) ℝ).PosDef} = Set.univ := by
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨selfAdjoint.isHermitian_coe A,
        fun x hx ↦ (hx (Subsingleton.elim x 0)).elim⟩
    rw [hgram, hcone, Measure.restrict_univ]
    simp [multivariateGamma_zero]
  set w : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ≥0∞ := fun A ↦
    ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n - p - 1) / 2) *
      exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace / 2) /
        (2 ^ (n * p / 2) * multivariateGamma p (n / 2))) with hw_def
  have hcoe : Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (A : Matrix (Fin p) (Fin p) ℝ) := continuous_subtype_val
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp <| (((hcoe.matrix_det.measurable.pow_const _).mul
      (hcoe.matrix_trace.neg.div_const _).rexp.measurable)).div_const _
  have hpi : Measure.pi (bartlettCoordinateMeasure (p := p) n) =
      volume.withDensity fun x ↦ ∏ ij, ENNReal.ofReal (bartlettCoordinatePDFReal n ij (x ij)) := by
    rw [funext (bartlettCoordinateMeasure_eq_withDensity n), volume_pi,
      pi_withDensity _ fun ij ↦ (measurable_bartlettCoordinatePDFReal n ij).ennreal_ofReal]
  have hgram := measurable_lowerTriangleGram p
  -- Both sides are integrals over the coordinate space: the left by definition of the
  -- pushforward, the right by the Cholesky change of variables. Compare the integrands.
  ext s hs
  rw [Measure.map_apply hgram hs, hpi, withDensity_apply _ (hgram hs), withDensity_apply _ hs,
    ← lintegral_indicator hs, setLIntegral_posDef_symmetricLebesgue p (hw.indicator hs),
    ← lintegral_indicator (hgram hs), ← lintegral_indicator (measurableSet_posDiagLowerRegion p)]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : x ∈ posDiagLowerRegion p
  · rw [Set.indicator_of_mem hx]
    by_cases hxs : lowerTriangleGram p x ∈ s
    · rw [Set.indicator_of_mem (Set.mem_preimage.2 hxs),
        Set.indicator_of_mem hxs, ← ENNReal.ofReal_prod_of_nonneg
          fun ij _ ↦ bartlettCoordinatePDFReal_nonneg hn ij (x ij),
        prod_bartlettCoordinatePDFReal hx, choleskyJacobianDensity_def, hw_def,
        ENNReal.ofReal_mul (mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ ↦
          pow_nonneg ((mem_posDiagLowerRegion p).1 hx i).le _))]
      simp only [coe_lowerTriangleGram]
    · rw [Set.indicator_of_notMem (Set.mem_preimage.not.2 hxs),
        Set.indicator_of_notMem hxs, mul_zero]
  · rw [Set.indicator_of_notMem hx, Set.indicator_apply_eq_zero]
    intro _
    rw [← ENNReal.ofReal_prod_of_nonneg fun ij _ ↦ bartlettCoordinatePDFReal_nonneg hn ij (x ij),
      prod_bartlettCoordinatePDFReal_of_notMem hx, ENNReal.ofReal_zero]

/-- Every Cholesky coordinate of a standard Wishart matrix of degree `n` follows a probability
law: a strictly lower coordinate is standard Gaussian, and the diagonal coordinate at `i` has the
chi law with the positive number `n - i` of degrees of freedom. -/
theorem isProbabilityMeasure_bartlettCoordinateMeasure (hn : (p : ℝ) - 1 < n)
    (ij : lowerTriangle p) : IsProbabilityMeasure (bartlettCoordinateMeasure n ij) := by
  by_cases hd : ij.1.1 = ij.1.2
  · rw [bartlettCoordinateMeasure_of_eq n hd]
    refine Probability.isProbabilityMeasure_withDensity_chi ?_
    have hlt : ((ij.1.1 : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt ij.1.1.isLt
    linarith
  · rw [bartlettCoordinateMeasure_of_ne n hd]
    infer_instance

/-- **Almost every vector of Cholesky coordinates of a standard Wishart matrix has positive
diagonal**, each diagonal coordinate carrying the chi law of the positive half-line. That is the
region on which the coordinates are the Cholesky factor of their Gram matrix. -/
theorem ae_mem_posDiagLowerRegion_pi_bartlettCoordinateMeasure (hn : (p : ℝ) - 1 < n) :
    ∀ᵐ x ∂(Measure.pi (bartlettCoordinateMeasure (p := p) n)), x ∈ posDiagLowerRegion p := by
  have : ∀ ij : lowerTriangle p, IsProbabilityMeasure (bartlettCoordinateMeasure n ij) :=
    fun ij => isProbabilityMeasure_bartlettCoordinateMeasure hn ij
  simp only [mem_posDiagLowerRegion]
  rw [ae_all_iff]
  intro i
  have hae : ∀ᵐ t ∂(bartlettCoordinateMeasure (p := p) n ⟨(i, i), le_rfl⟩), 0 < t := by
    rw [bartlettCoordinateMeasure_of_eq n rfl]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  refine ae_of_ae_map (f := Function.eval (⟨(i, i), le_rfl⟩ : lowerTriangle p))
    (measurable_pi_apply _).aemeasurable ?_
  rw [(measurePreserving_eval (μ := bartlettCoordinateMeasure (p := p) n)
    (⟨(i, i), le_rfl⟩ : lowerTriangle p)).map_eq]
  exact hae

/-- **The standard Wishart law is the Gram law of its Cholesky coordinates.** For a degree above
`p - 1` the law `TauCeti.nonsingularWishartMeasure n 1` is the image, under `L ↦ L * Lᵀ`, of
independent Cholesky coordinates with the chi and standard Gaussian laws. -/
theorem nonsingularWishartMeasure_one_eq_map_lowerTriangleGram (hn : (p : ℝ) - 1 < n) :
    nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) =
      (Measure.pi (bartlettCoordinateMeasure (p := p) n)).map (lowerTriangleGram p) := by
  classical
  rw [map_lowerTriangleGram_pi_bartlettCoordinateMeasure (Or.inr hn),
    nonsingularWishartMeasure_of_posDef Matrix.PosDef.one hn,
    ← withDensity_indicator (measurableSet_posDefMatrix p)]
  congr 1
  funext A
  rw [Set.indicator_apply]
  split_ifs with hA
  · rw [nonsingularWishartPDF_def, nonsingularWishartPDFReal_of_posDef n 1 hA]
    simp
  · exact nonsingularWishartPDF_of_not_posDef n 1 hA

end TauCeti
