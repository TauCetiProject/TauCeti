/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Distributions.Gaussian.Pi

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The density of a multivariate Gaussian measure

A multivariate Gaussian law with positive-definite covariance `S` is Lebesgue measure on
`EuclideanSpace ℝ ι` weighted by the classical density

`(2π)^(-d/2) * (det S)^(-1/2) * exp (-⟪x - m, S⁻¹ (x - m)⟫ / 2)`,

where `d` is the dimension. Every other covariance parameter gives a law carried by a proper
affine subspace, so it is singular with respect to Lebesgue measure and has no density against
it.

The nondegenerate case comes from the isotropic product density
(`TauCeti.pi_gaussianReal_eq_withDensity`) by an affine change of variables along the square root
of the covariance, which contributes the Jacobian `√(det S)` and turns the isotropic quadratic
form into the one of `S⁻¹`.

## Main definitions

* `TauCeti.multivariateGaussianPDFReal` — the real-valued density;
* `TauCeti.multivariateGaussianPDF` — its `ℝ≥0∞`-valued companion.

## Main results

* `TauCeti.stdGaussian_eq_withDensity` — the standard Gaussian on `EuclideanSpace ℝ ι` is Lebesgue
  measure weighted by `(2π)^(-d/2) * exp (-‖x‖² / 2)`;
* `TauCeti.multivariateGaussian_eq_withDensity` — the density presentation of the law;
* `TauCeti.hasPDF_of_hasLaw_multivariateGaussian` and
  `TauCeti.pdf_eq_multivariateGaussianPDF_of_hasLaw_multivariateGaussian` — the `HasPDF` bridge
  and the identification of `MeasureTheory.pdf`;
* `TauCeti.rnDeriv_multivariateGaussian` — the Radon–Nikodym derivative;
* `TauCeti.mutuallySingular_multivariateGaussian_volume` — singularity at every covariance
  parameter that is not positive definite.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **density of the multivariate Gaussian law** with mean `m` and covariance `S`, as a real
number. It is the density of `multivariateGaussian m S` when `S` is positive definite
(`TauCeti.multivariateGaussian_eq_withDensity`); at every other `S` that law has no density with
respect to Lebesgue measure (`TauCeti.mutuallySingular_multivariateGaussian_volume`). -/
def multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2) *
    exp (-⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫ / 2)

/-- The `ℝ≥0∞`-valued companion to `TauCeti.multivariateGaussianPDFReal`. -/
def multivariateGaussianPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal (multivariateGaussianPDFReal m S x)

variable {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}

/-- The defining formula of the real-valued density. -/
theorem multivariateGaussianPDFReal_def (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    multivariateGaussianPDFReal m S = fun x => (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) *
      S.det ^ (-(1 : ℝ) / 2) * exp (-⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫ / 2) := (rfl)

/-- The `ℝ≥0∞`-valued density is the `ENNReal.ofReal` lift of the real-valued one. -/
theorem multivariateGaussianPDF_def (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    multivariateGaussianPDF m S =
      fun x => ENNReal.ofReal (multivariateGaussianPDFReal m S x) := (rfl)

/-- The density is positive wherever the determinant is, in particular at a positive-definite
covariance, where `Matrix.PosDef.det_pos` supplies the hypothesis. -/
theorem multivariateGaussianPDFReal_pos (hdet : 0 < S.det) (m : EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : 0 < multivariateGaussianPDFReal m S x := by
  have hπ : 0 < 2 * π := by positivity
  rw [multivariateGaussianPDFReal]
  positivity

/-- The real-valued density is nonnegative at every covariance parameter. At a negative
determinant the real power `S.det ^ (-1/2)` vanishes, so the density is `0` there. -/
theorem multivariateGaussianPDFReal_nonneg (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : 0 ≤ multivariateGaussianPDFReal m S x := by
  have hdet : 0 ≤ S.det ^ (-(1 : ℝ) / 2) := by
    rcases le_or_gt 0 S.det with h | h
    · exact Real.rpow_nonneg h _
    -- at a negative base the real power is `exp (log · * y) * cos (y * π)`, which vanishes at
    -- the exponent `y = -1/2`
    · have harg : -(1 : ℝ) / 2 * π = -(π / 2) := by ring
      rw [Real.rpow_def_of_neg h, harg, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  have hπ : (0 : ℝ) ≤ (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  rw [multivariateGaussianPDFReal]
  exact mul_nonneg (mul_nonneg hπ hdet) (Real.exp_nonneg _)

/-- The `ℝ≥0∞`-valued density is positive wherever the determinant is. -/
theorem multivariateGaussianPDF_pos (hdet : 0 < S.det) (m : EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : 0 < multivariateGaussianPDF m S x :=
  ENNReal.ofReal_pos.mpr (multivariateGaussianPDFReal_pos hdet m x)

/-- The `ℝ≥0∞`-valued density is finite at every covariance parameter. -/
@[simp]
theorem multivariateGaussianPDF_ne_top (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : multivariateGaussianPDF m S x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The `ℝ≥0∞`-valued density is finite at every covariance parameter. -/
theorem multivariateGaussianPDF_lt_top (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : multivariateGaussianPDF m S x < ⊤ :=
  ENNReal.ofReal_lt_top

/-- The `ℝ≥0∞`-valued density carries the real-valued one back through `ENNReal.toReal`. -/
@[simp]
theorem toReal_multivariateGaussianPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    (multivariateGaussianPDF m S x).toReal = multivariateGaussianPDFReal m S x := by
  rw [multivariateGaussianPDF, ENNReal.toReal_ofReal (multivariateGaussianPDFReal_nonneg m S x)]

/-- The real-valued density is measurable. -/
@[fun_prop]
theorem measurable_multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measurable (multivariateGaussianPDFReal m S) := by
  unfold multivariateGaussianPDFReal
  fun_prop

/-- The `ℝ≥0∞`-valued density is measurable. -/
@[fun_prop]
theorem measurable_multivariateGaussianPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measurable (multivariateGaussianPDF m S) :=
  (measurable_multivariateGaussianPDFReal m S).ennreal_ofReal

omit [DecidableEq ι] in
/-- **The standard Gaussian on `EuclideanSpace ℝ ι` has the isotropic Gaussian density.** -/
theorem stdGaussian_eq_withDensity :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity fun x =>
        ENNReal.ofReal ((2 * π) ^ (-(Fintype.card ι : ℝ) / 2) * exp (-‖x‖ ^ 2 / 2)) := by
  have hvol : (volume : Measure (ι → ℝ)).map ⇑(MeasurableEquiv.toLp 2 (ι → ℝ)) = volume :=
    (PiLp.volume_preserving_toLp ι).map_eq
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity,
    ← MeasurableEquiv.coe_toLp 2 (ι → ℝ), MeasurableEquiv.map_withDensity, ← volume_pi, hvol]
  refine withDensity_congr_ae (.of_forall fun y => congrArg ENNReal.ofReal ?_)
  rw [prod_gaussianPDFReal_zero_one, MeasurableEquiv.coe_toLp_symm,
    ← EuclideanSpace.real_norm_sq_eq]

/-- **A nondegenerate multivariate Gaussian law is Lebesgue measure with the Gaussian density.** -/
theorem multivariateGaussian_eq_withDensity (hS : S.PosDef) (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m S = volume.withDensity (multivariateGaussianPDF m S) := by
  -- The square root of `S` gives the affine substitution `x ↦ m + √S x` carrying the standard
  -- Gaussian to this one; `Measure.map_affine_withDensity` transports the density along it, and
  -- the inverse square root turns the isotropic quadratic form into the one of `S⁻¹`.
  have hR : (CFC.sqrt S).PosSemidef := Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)
  have hRR : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hdetS : 0 < S.det := hS.det_pos
  have hdetR : (CFC.sqrt S).det = √S.det := by simpa using hS.posSemidef.det_sqrt
  have hdetRpos : 0 < (CFC.sqrt S).det := by rw [hdetR]; positivity
  have hRunit : (CFC.sqrt S).det ≠ 0 := hdetRpos.ne'
  have hCLM : ∀ (X : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι),
      Matrix.toEuclideanCLM (𝕜 := ℝ) X z = X.toEuclideanLin z := fun X z => by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin X, ContinuousLinearMap.coe_coe]
  -- the square root is invertible, so it induces a continuous linear equivalence
  have hAfun : (fun x : EuclideanSpace ℝ ι => m + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
      = fun x => m + Matrix.toEuclideanCLE (CFC.sqrt S) hRunit x :=
    funext fun x => by rw [hCLM, Matrix.toEuclideanCLE_apply]
  -- the inverse square root pulls the isotropic quadratic form back to the one of `S⁻¹`
  have hconj : ((CFC.sqrt S)⁻¹).conjTranspose * 1 * (CFC.sqrt S)⁻¹ = S⁻¹ := by
    rw [mul_one, hR.isHermitian.inv.eq, ← Matrix.mul_inv_rev, hRR]
  have hnorm : ∀ z : EuclideanSpace ℝ ι,
      ‖(CFC.sqrt S)⁻¹.toEuclideanLin z‖ ^ 2 = ⟪z, S⁻¹.toEuclideanLin z⟫ :=
    fun z => by
      rw [← real_inner_self_eq_norm_sq, ← hconj,
        ← Matrix.inner_toEuclideanLin_toEuclideanLin (CFC.sqrt S)⁻¹ 1 z]
      simp
  have hrpow : S.det ^ (-(1 : ℝ) / 2) = (√S.det)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hdetS.le]
    congr 1
    ring
  rw [multivariateGaussian, stdGaussian_eq_withDensity, hAfun, Measure.map_affine_withDensity,
    Matrix.det_toEuclideanCLE]
  refine withDensity_congr_ae (.of_forall fun y => ?_)
  simp only [multivariateGaussianPDF, multivariateGaussianPDFReal,
    Matrix.toEuclideanCLE_symm_apply]
  rw [← ENNReal.ofReal_mul (by positivity), hnorm, abs_of_pos (by positivity), hdetR, hrpow]
  congr 1
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}

/-- A random vector with a nondegenerate multivariate Gaussian law has a density. -/
theorem hasPDF_of_hasLaw_multivariateGaussian (hS : S.PosDef)
    (hX : HasLaw X (multivariateGaussian m S) P) : HasPDF X P :=
  Probability.hasPDF_of_hasLaw_withDensity (measurable_multivariateGaussianPDF m S).aemeasurable
    (by rwa [← multivariateGaussian_eq_withDensity hS])

/-- The density of a nondegenerate multivariate Gaussian law is `multivariateGaussianPDF`. -/
theorem pdf_eq_multivariateGaussianPDF_of_hasLaw_multivariateGaussian (hS : S.PosDef)
    (hX : HasLaw X (multivariateGaussian m S) P) :
    pdf X P =ᵐ[volume] multivariateGaussianPDF m S :=
  Probability.pdf_eq_of_hasLaw_withDensity (measurable_multivariateGaussianPDF m S).aemeasurable
    (by rwa [← multivariateGaussian_eq_withDensity hS])

/-- **The Radon–Nikodym derivative of a nondegenerate multivariate Gaussian law.** -/
theorem rnDeriv_multivariateGaussian (hS : S.PosDef) (m : EuclideanSpace ℝ ι) :
    (multivariateGaussian m S).rnDeriv volume =ᵐ[volume] multivariateGaussianPDF m S := by
  rw [multivariateGaussian_eq_withDensity hS]
  exact Measure.rnDeriv_withDensity _ (measurable_multivariateGaussianPDF m S)

/-- **Every degenerate multivariate Gaussian law is singular.** A positive-semidefinite but
singular covariance carries the law on the proper affine subspace `m + range (CFC.sqrt S)`; any
other covariance makes the law a point mass. -/
theorem mutuallySingular_multivariateGaussian_volume (hS : ¬ S.PosDef)
    (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m S ⟂ₘ (volume : Measure (EuclideanSpace ℝ ι)) := by
  -- over an empty index type every matrix is positive definite, so the index type is nonempty
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hS ⟨by ext i; exact isEmptyElim i,
      fun x hx => absurd (Finsupp.ext fun i => isEmptyElim i) hx⟩
  by_cases hSS : S.PosSemidef
  · have hdet0 : (CFC.sqrt S).det = 0 := by
      have hS0 : S.det = 0 := by
        by_contra hd
        exact hS (hSS.posDef_iff_det_ne_zero.mpr hd)
      simp [hSS.det_sqrt, hS0]
    set p : Submodule ℝ (EuclideanSpace ℝ ι) :=
      LinearMap.range (Matrix.toEuclideanLin (CFC.sqrt S)) with hp
    have hptop : p ≠ ⊤ :=
      (LinearMap.range_lt_top_of_det_eq_zero (by rw [LinearMap.det_toLpLin]; exact hdet0)).ne
    -- the law is carried by the proper affine subspace through `m` with direction `p`
    set A : AffineSubspace ℝ (EuclideanSpace ℝ ι) := AffineSubspace.mk' m p with hA
    have hAtop : A ≠ ⊤ := fun h => hptop <| by
      rw [← AffineSubspace.direction_mk' m p, ← hA, h, AffineSubspace.direction_top]
    have hAc : MeasurableSet (A : Set (EuclideanSpace ℝ ι))ᶜ :=
      A.closed_of_finiteDimensional.measurableSet.compl
    refine ⟨(A : Set (EuclideanSpace ℝ ι))ᶜ, hAc, ?_, ?_⟩
    · rw [multivariateGaussian, Measure.map_apply (by fun_prop) hAc]
      convert measure_empty (μ := stdGaussian (EuclideanSpace ℝ ι))
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not,
        hA, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub,
        add_sub_cancel_left, hp]
      exact LinearMap.mem_range_self _ x
    · rw [compl_compl]
      exact Measure.addHaar_affineSubspace volume A hAtop
  · rw [multivariateGaussian_of_not_posSemidef m hSS]
    exact mutuallySingular_dirac m volume

/-- A degenerate multivariate Gaussian law has vanishing Radon–Nikodym derivative. -/
theorem rnDeriv_multivariateGaussian_of_not_posDef (hS : ¬ S.PosDef)
    (m : EuclideanSpace ℝ ι) :
    (multivariateGaussian m S).rnDeriv volume =ᵐ[volume] 0 :=
  Measure.MutuallySingular.rnDeriv_ae_eq_zero
    (mutuallySingular_multivariateGaussian_volume hS m)

end TauCeti
