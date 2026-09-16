/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Cholesky
public import Mathlib.Probability.Distributions.Gaussian.Real

import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# The standard Wishart density in Cholesky coordinates

A positive-definite symmetric `p × p` matrix `A` is `L * Lᵀ` for a unique lower-triangular `L`
with positive diagonal. This file shows that the standard Wishart density of real degree `n`,

`(det A) ^ ((n - p - 1) / 2) * exp (-trace A / 2) / (2 ^ (n * p / 2) * Γ_p (n / 2))`

against `TauCeti.symmetricLebesgue p` on the positive-definite cone, becomes a product density in
the entries of `L`. Precisely, take independent real coordinates indexed by the on-or-below
diagonal positions `(i, j)`, `j ≤ i`, of a `p × p` matrix, where

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

* `TauCeti.bartlettCoordinateMeasure` — the law of one Cholesky coordinate.
* `TauCeti.map_lowerTriangleGram_pi_bartlettCoordinateMeasure` — the Gram matrix of independent
  coordinates with these laws has the standard Wishart density.

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

/-- The law of the Cholesky coordinate at the on-or-below-diagonal position `ij` of a standard
Wishart matrix of real degree `n`: the diagonal coordinate `(i, i)` has the chi density with
`n - i` degrees of freedom on the positive half-line, and a strictly lower coordinate is a
standard Gaussian. -/
def bartlettCoordinateMeasure (n : ℝ) (ij : lowerTriangle p) : Measure ℝ :=
  if ij.1.1 = ij.1.2 then
    (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
      ((2 : ℝ) ^ (1 - (n - ij.1.1) / 2) / Real.Gamma ((n - ij.1.1) / 2) *
        t ^ (n - ij.1.1 - 1) * exp (-t ^ 2 / 2))
  else gaussianReal 0 1

/-- A diagonal Cholesky coordinate has the chi density with `n - i` degrees of freedom. -/
theorem bartlettCoordinateMeasure_of_eq (n : ℝ) {ij : lowerTriangle p} (h : ij.1.1 = ij.1.2) :
    bartlettCoordinateMeasure n ij =
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
        ((2 : ℝ) ^ (1 - (n - ij.1.1) / 2) / Real.Gamma ((n - ij.1.1) / 2) *
          t ^ (n - ij.1.1 - 1) * exp (-t ^ 2 / 2)) :=
  ite_eq_left_iff.2 fun h' ↦ absurd h h'

/-- A strictly lower Cholesky coordinate is standard Gaussian. -/
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
  have hpow : (2 : ℝ) ^ (1 - (n - i) / 2) = 2 * 2 ^ ((i : ℝ) / 2) / 2 ^ (n / 2) := by
    rw [show (1 : ℝ) - (n - i) / 2 = 1 + (i : ℝ) / 2 - n / 2 by ring, Real.rpow_sub h2,
      Real.rpow_add h2, Real.rpow_one]
  rw [inv_pow, hsqrt, hpow, show (n - i) / 2 = n / 2 - (i : ℝ) / 2 by ring]
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
  -- Each diagonal coordinate carries the determinant power and its Jacobian power together.
  have hkey : ∀ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - i.1) *
      x ⟨(i, i), le_rfl⟩ ^ (n - p - 1) = x ⟨(i, i), le_rfl⟩ ^ (n - i.1 - 1) := by
    intro i
    rw [← Real.rpow_natCast (x ⟨(i, i), le_rfl⟩) (p - i.1), ← Real.rpow_add (hpos i),
      Nat.cast_sub i.2.le]
    congr 1
    ring
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin p)), (0 : ℝ) ≤ x ⟨(i, i), le_rfl⟩ :=
    fun i _ ↦ (hpos i).le
  have hdet : (lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).det ^ ((n - p - 1) / 2) =
      ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (n - p - 1) := by
    rw [Matrix.det_mul, Matrix.det_transpose, det_lowerTriangleMatrix, ← pow_two,
      ← Real.rpow_natCast (∏ i : Fin p, x ⟨(i, i), le_rfl⟩) 2,
      ← Real.rpow_mul (Finset.prod_nonneg hnn), ← Real.finsetProd_rpow _ _ hnn]
    congr 1
    funext i
    rw [show ((2 : ℕ) : ℝ) * ((n - p - 1) / 2) = n - p - 1 by push_cast; ring]
  have htwo : (2 : ℝ) ^ (n * p / 2) = ∏ _i : Fin p, (2 : ℝ) ^ (n / 2) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul two_pos.le]
    ring_nf
  have hexp : ∏ ij : lowerTriangle p, exp (-x ij ^ 2 / 2) =
      exp (-(lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ).trace / 2) := by
    rw [← Real.exp_sum, trace_lowerTriangleMatrix_mul_transpose, neg_div, Finset.sum_div,
      ← Finset.sum_neg_distrib]
    simp only [neg_div]
  rw [Finset.prod_congr rfl fun ij _ ↦ hfac ij, Finset.prod_mul_distrib, hexp,
    prod_lowerTriangle_ite
      (fun i ↦ (2 : ℝ) ^ (1 - (n - i.1) / 2) / Real.Gamma ((n - i.1) / 2) *
        x ⟨(i, i), le_rfl⟩ ^ (n - i.1 - 1)) fun _ ↦ (√(2 * π))⁻¹,
    hdet, multivariateGamma_eq_prod, htwo]
  have hrow : ∀ i : Fin p,
      (2 : ℝ) ^ (1 - (n - i.1) / 2) / Real.Gamma ((n - i.1) / 2) *
          x ⟨(i, i), le_rfl⟩ ^ (n - i.1 - 1) * (√(2 * π))⁻¹ ^ i.1 =
        x ⟨(i, i), le_rfl⟩ ^ (n - i.1 - 1) * 2 /
          (2 ^ (n / 2) * π ^ ((i.1 : ℝ) / 2) * Real.Gamma (n / 2 - (i.1 : ℝ) / 2)) := by
    intro i
    rw [mul_right_comm, bartlett_row_const]
    ring
  rw [Finset.prod_congr rfl fun i _ ↦ hrow i]
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Finset.prod_congr rfl fun i _ ↦ hkey i, Finset.prod_mul_distrib]
  ring

/-- For `(p : ℝ) - 1 < n` every chi coordinate has positive degrees of freedom, so the coordinate
densities are nonnegative. -/
private theorem bartlettCoordinatePDFReal_nonneg (hn : (p : ℝ) - 1 < n) (ij : lowerTriangle p)
    (t : ℝ) : 0 ≤ bartlettCoordinatePDFReal n ij t := by
  unfold bartlettCoordinatePDFReal
  split_ifs
  · refine Set.indicator_nonneg (fun t (ht : 0 < t) ↦ ?_) t
    have hi : ((ij.1.1 : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast ij.1.1.2
    have := Real.Gamma_pos_of_pos (show 0 < (n - ij.1.1) / 2 by linarith)
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
density with `n - i` degrees of freedom and each strictly lower entry standard Gaussian. For
`(p : ℝ) - 1 < n`, the symmetric matrix `L * Lᵀ` then has the standard Wishart density of degree
`n`, `(det A) ^ ((n - p - 1) / 2) * exp (-trace A / 2) / (2 ^ (n * p / 2) * Γ_p (n / 2))` on the
positive-definite cone, against `TauCeti.symmetricLebesgue p`. -/
theorem map_lowerTriangleGram_pi_bartlettCoordinateMeasure (hn : (p : ℝ) - 1 < n) :
    (Measure.pi (bartlettCoordinateMeasure (p := p) n)).map (lowerTriangleGram p) =
      ((symmetricLebesgue p).restrict
          {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
            (A : Matrix (Fin p) (Fin p) ℝ).PosDef}).withDensity fun A ↦
        ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ ((n - p - 1) / 2) *
          exp (-(A : Matrix (Fin p) (Fin p) ℝ).trace / 2) /
            (2 ^ (n * p / 2) * multivariateGamma p (n / 2))) := by
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

end TauCeti
