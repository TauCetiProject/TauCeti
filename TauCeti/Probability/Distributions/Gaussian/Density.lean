/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Sqrt
public import TauCeti.MeasureTheory.Measure.Support
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
(`TauCeti.Probability.pi_gaussianReal_eq_withDensity`) by an affine change of variables along the
square root
of the covariance, which contributes the Jacobian `√(det S)` and turns the isotropic quadratic
form into the one of `S⁻¹`.

## Main definitions

* `TauCeti.Probability.multivariateGaussianPDFReal` — the real-valued density;
* `TauCeti.Probability.multivariateGaussianPDF` — its `ℝ≥0∞`-valued companion.

## Main results

* `TauCeti.Probability.stdGaussian_eq_withDensity` — the standard Gaussian on `EuclideanSpace ℝ ι`
  is Lebesgue
  measure weighted by `(2π)^(-d/2) * exp (-‖x‖² / 2)`;
* `TauCeti.Probability.stdGaussian_eq_withDensity_norm` — the same density on any
  finite-dimensional real inner product space;
* `TauCeti.Probability.support_multivariateGaussian` — the support at a positive-semidefinite
  covariance is the affine range `m + range S`;
* `TauCeti.Probability.ae_mem_affineRange_multivariateGaussian` — the law is almost surely in
  this affine range;
* `TauCeti.Probability.multivariateGaussian_eq_withDensity` — the density presentation of the law;
* `TauCeti.Probability.hasPDF_of_hasLaw_multivariateGaussian` and
  `TauCeti.Probability.pdf_eq_multivariateGaussianPDF_of_hasLaw_multivariateGaussian` — the `HasPDF`
  bridge
  and the identification of `MeasureTheory.pdf`;
* `TauCeti.Probability.rnDeriv_multivariateGaussian` — the Radon–Nikodym derivative;
* `TauCeti.Probability.mutuallySingular_multivariateGaussian_volume` — singularity at every
  covariance
  parameter that is not positive definite.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **density of the multivariate Gaussian law** with mean `m` and covariance `S`, as a real
number. It is the density of `multivariateGaussian m S` when `S` is positive definite
(`TauCeti.Probability.multivariateGaussian_eq_withDensity`); at every other `S` that law has no
density with
respect to Lebesgue measure (`TauCeti.Probability.mutuallySingular_multivariateGaussian_volume`). -/
def multivariateGaussianPDFReal (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2) *
    exp (-⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫ / 2)

/-- The `ℝ≥0∞`-valued companion to `TauCeti.Probability.multivariateGaussianPDFReal`. -/
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

/-- **The standard Gaussian on a finite-dimensional real inner product space has the isotropic
Gaussian density** `(2π)^(-d/2) * exp (-‖x‖² / 2)`, where `d` is the dimension. -/
theorem stdGaussian_eq_withDensity_norm (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    stdGaussian E =
      volume.withDensity fun x =>
        ENNReal.ofReal ((2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) * exp (-‖x‖ ^ 2 / 2)) := by
  -- Transport the Euclidean density along an orthonormal basis, which preserves volume and norms.
  let b := (stdOrthonormalBasis ℝ E).repr
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).map b.symm =
      volume :=
    b.symm.measurePreserving.map_eq
  have htransport : ∀ g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞,
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).withDensity g).map
          b.symm =
        (volume : Measure E).withDensity fun x => g (b x) := fun g => by
    simpa [hvol] using b.symm.toMeasurableEquiv.map_withDensity volume g
  rw [← stdGaussian_map b.symm, stdGaussian_eq_withDensity, htransport]
  congr 1
  funext x
  simp

/-- The standard Gaussian measure on a finite-dimensional real inner product space has full
support. -/
@[simp]
theorem support_stdGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    (stdGaussian E).support = Set.univ := by
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ E).repr.symm
  have hsupport : (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).support =
      Set.univ := by
    rw [stdGaussian_eq_withDensity]
    let f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞ := fun x =>
      ENNReal.ofReal
        ((2 * π) ^ (-(Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) / 2) * exp (-‖x‖ ^ 2 / 2))
    have hf : Measurable f := by
      fun_prop
    have hsupp : Function.support f = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true, ne_eq, ENNReal.ofReal_eq_zero,
        not_le, f]
      positivity
    simpa only [f, closure_univ] using
      (Measure.support_withDensity_eq_closure (μ := volume) hf isOpen_univ hsupp)
  rw [← stdGaussian_map e]
  rw [← e.coe_toHomeomorph]
  rw [Measure.support_map_homeomorph, hsupport]
  exact Set.image_univ_of_surjective e.surjective

/-- The support of a multivariate Gaussian measure with positive-semidefinite covariance is the
affine range of its covariance. -/
@[simp]
theorem support_multivariateGaussian (hS : S.PosSemidef) (m : EuclideanSpace ℝ ι) :
    (multivariateGaussian m S).support =
      (AffineSubspace.mk' m (LinearMap.range (Matrix.toEuclideanLin S)) :
        Set (EuclideanSpace ℝ ι)) := by
  rw [multivariateGaussian,
    Measure.support_map_eq_closure_range _ (support_stdGaussian (EuclideanSpace ℝ ι))
      (by fun_prop),
    ← hS.range_toEuclideanLin_sqrt]
  let A : AffineSubspace ℝ (EuclideanSpace ℝ ι) :=
    AffineSubspace.mk' m (LinearMap.range (Matrix.toEuclideanLin (CFC.sqrt S)))
  have hAclosed : IsClosed (A : Set (EuclideanSpace ℝ ι)) := A.closed_of_finiteDimensional
  have hrange : Set.range (fun x => m + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) =
      (A : Set (EuclideanSpace ℝ ι)) := by
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, A]
    constructor
    · rintro ⟨x, rfl⟩
      rw [Matrix.toEuclideanCLM_apply, add_sub_cancel_left]
      exact LinearMap.mem_range_self _ x
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [Matrix.toEuclideanCLM_apply, hx]
      abel
  rw [hrange, hAclosed.closure_eq]

/-- A multivariate Gaussian measure with positive-semidefinite covariance is almost surely in the
affine range of its covariance. -/
theorem ae_mem_affineRange_multivariateGaussian (hS : S.PosSemidef)
    (m : EuclideanSpace ℝ ι) :
    ∀ᵐ x ∂multivariateGaussian m S,
      x ∈ (AffineSubspace.mk' m (LinearMap.range (Matrix.toEuclideanLin S)) :
        Set (EuclideanSpace ℝ ι)) := by
  exact Filter.eventually_mem_set.mpr <|
    support_multivariateGaussian hS m ▸ (multivariateGaussian m S).support_mem_ae

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
  -- the square root is invertible, so it induces a continuous linear equivalence
  have hAfun : (fun x : EuclideanSpace ℝ ι => m + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
      = fun x => m + Matrix.toEuclideanCLE (CFC.sqrt S) hRunit x :=
    funext fun x => by rw [Matrix.toEuclideanCLM_apply, Matrix.toEuclideanCLE_apply]
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
  · have hdet0 : S.det = 0 := by
      by_contra hd
      exact hS (hSS.posDef_iff_det_ne_zero.mpr hd)
    set p : Submodule ℝ (EuclideanSpace ℝ ι) :=
      LinearMap.range (Matrix.toEuclideanLin S) with hp
    have hptop : p ≠ ⊤ :=
      (LinearMap.range_lt_top_of_det_eq_zero (by rw [LinearMap.det_toLpLin]; exact hdet0)).ne
    -- the law is carried by the proper affine subspace through `m` with direction `p`
    set A : AffineSubspace ℝ (EuclideanSpace ℝ ι) := AffineSubspace.mk' m p with hA
    have hAtop : A ≠ ⊤ := fun h => hptop <| by
      rw [← AffineSubspace.direction_mk' m p, ← hA, h, AffineSubspace.direction_top]
    have hAc : MeasurableSet (A : Set (EuclideanSpace ℝ ι))ᶜ :=
      A.closed_of_finiteDimensional.measurableSet.compl
    refine ⟨(A : Set (EuclideanSpace ℝ ι))ᶜ, hAc, ?_, ?_⟩
    · simpa only [hA, hp] using
        mem_ae_iff.mp (Filter.eventually_mem_set.mp (ae_mem_affineRange_multivariateGaussian hSS m))
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

end TauCeti.Probability
