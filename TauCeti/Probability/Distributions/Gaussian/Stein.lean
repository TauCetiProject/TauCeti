/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Density
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.Probability.Moments.Covariance

/-!
# Stein's identity for the isotropic Gaussian law

For the isotropic Gaussian law `N(θ, v I)` on `EuclideanSpace ℝ ι`, `v ≥ 0`, and a
differentiable `f`, Stein's identity in the coordinate `i` reads

`E[(Xᵢ - θᵢ) f(X)] = v E[∂ᵢ f(X)]`,

under integrability of `f`, of `(xᵢ - θᵢ) f` and of `∂ᵢ f`. Applied to the coordinates of a
vector field `g ∈ L²` it gives `E[(Xᵢ - θᵢ) gᵢ(X)] = v E[∂ᵢ gᵢ(X)]`. For `v > 0` the proof
writes the law as Lebesgue measure with the density `c exp (-‖x - θ‖² / (2v))` and integrates by
parts against it along `eᵢ`; at `v = 0` the law is the point mass at `θ` and both sides vanish.
The one-dimensional identity is
`TauCeti.Probability.integral_sub_smul_eq_smul_integral_deriv_gaussianReal`.

The file also records a closed form of `multivariateGaussianPDFReal θ (v I)` for `v ≥ 0` (a
density of `N(θ, v I)` when `v > 0`), the mean squared distance `E‖X - m‖² = tr S` of every
multivariate Gaussian law, and the integrability of `(‖x‖ ^ 2)⁻¹` under `N(θ, v I)` in dimension
at least `3`. Here `(‖x‖ ^ 2)⁻¹` is the real-valued reciprocal, which takes the value `0` at the
origin; for `v ≤ 0`, where `multivariateGaussian` falls back to the point mass at `θ`, this
convention matters when `θ = 0`.

## Main results

* `TauCeti.Probability.multivariateGaussianPDFReal_smul_one`: for `v ≥ 0`,
  `multivariateGaussianPDFReal θ (v I) x = (2π v)^(-d/2) exp (-‖x - θ‖² / (2v))`, where `d` is
  the dimension; for `v > 0` this is the density of `N(θ, v I)`.
* `TauCeti.Probability.multivariateGaussian_smul_one_eq_withDensity`: `N(θ, v I)`, `v > 0`, as a
  law with this density.
* `TauCeti.Probability.integral_norm_sub_sq_multivariateGaussian`: `E‖X - m‖² = tr S`.
* `TauCeti.Probability.integral_sub_mul_eq_mul_integral_fderiv_multivariateGaussian`: Stein's
  identity for a real function.
* `TauCeti.Probability.gaussian_integration_by_parts`: Stein's identity for the coordinates of an
  `L²` vector field.
* `TauCeti.Probability.integrable_inv_norm_sq_multivariateGaussian`: the real-valued reciprocal
  `(‖x‖ ^ 2)⁻¹` (equal to `0` at the origin) is integrable under `multivariateGaussian θ (v I)`
  for every real `v`, in dimension at least `3`.

## References

* M. J. Schervish, *Theory of Statistics*, Springer, 1995, Lemmas 3.51–3.52, pp. 163–164.
* C. Stein, *Estimation of the mean of a multivariate normal distribution*, Ann. Statist. 9
  (1981), 1135–1151.

The closed-form density and Stein's identity are adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>), file `CKSD/Inference/Gaussian.lean`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal RealInnerProductSpace MatrixOrder

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Closed form of `multivariateGaussianPDFReal θ (v I)` for `v ≥ 0`:
`(2π v)^(-d/2) exp (-‖x - θ‖² / (2v))`, where `d` is the dimension. For `v > 0` this is the
density of `N(θ, v I)` (see `multivariateGaussian_smul_one_eq_withDensity`). At `v = 0` it is
an identity of real expressions under Lean's conventions `0⁻¹ = 0` and `0 ^ r`; in positive
dimension it is then not a density of the point mass `N(θ, 0)`, while in dimension `0` the
expression is `1`, a density of the point mass. -/
theorem multivariateGaussianPDFReal_smul_one {v : ℝ} (hv : 0 ≤ v) (θ x : EuclideanSpace ℝ ι) :
    multivariateGaussianPDFReal θ (v • (1 : Matrix ι ι ℝ)) x =
      (2 * π * v) ^ (-(Fintype.card ι : ℝ) / 2) * exp (-‖x - θ‖ ^ 2 / (2 * v)) := by
  have hinv : (v • (1 : Matrix ι ι ℝ))⁻¹ = v⁻¹ • 1 := by
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    simpa [Units.smul_def] using
      Matrix.inv_smul' (Units.mk0 v hv0) (A := (1 : Matrix ι ι ℝ)) (by simp)
  have hdet : (v • (1 : Matrix ι ι ℝ)).det ^ (-(1 : ℝ) / 2) =
      v ^ (-(Fintype.card ι : ℝ) / 2) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, ← Real.rpow_natCast_mul hv]
    ring_nf
  rw [multivariateGaussianPDFReal_def, hdet, hinv, map_smul, Matrix.toLpLin_one, mul_rpow
    (by positivity) hv]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right,
    real_inner_self_eq_norm_sq]
  congr 2
  field_simp

/-- The mean squared distance of a multivariate Gaussian law from its mean is the trace of its
covariance: `E‖X - m‖² = tr S`. -/
theorem integral_norm_sub_sq_multivariateGaussian {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (m : EuclideanSpace ℝ ι) :
    ∫ x, ‖x - m‖ ^ 2 ∂multivariateGaussian m S = S.trace := by
  rw [TauCeti.integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix _
    IsGaussian.memLp_two_id m, integral_id_multivariateGaussian,
    covMatrix_multivariateGaussian m hS, sub_self, norm_zero, zero_pow two_ne_zero, zero_add]

/-- The isotropic Gaussian law `N(θ, v I)`, `v > 0`, is Lebesgue measure with the density
`(2π v)^(-d/2) exp (-‖x - θ‖² / (2v))`. -/
theorem multivariateGaussian_smul_one_eq_withDensity {v : ℝ} (hv : 0 < v)
    (θ : EuclideanSpace ℝ ι) :
    multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)) = volume.withDensity fun x ↦
      ENNReal.ofReal ((2 * π * v) ^ (-(Fintype.card ι : ℝ) / 2) *
        exp (-‖x - θ‖ ^ 2 / (2 * v))) := by
  rw [multivariateGaussian_eq_withDensity (Matrix.PosDef.one.smul hv),
    multivariateGaussianPDF_def]
  simp_rw [multivariateGaussianPDFReal_smul_one hv.le]

/-- For `v ≤ 0`, `multivariateGaussian θ (v I)` is the point mass at `θ`. At `v = 0` this is the
degenerate Gaussian law; for `v < 0` the matrix `v I` is not a covariance matrix (in positive
dimension) and this is the fallback value of `multivariateGaussian`. -/
theorem multivariateGaussian_smul_one_of_nonpos {v : ℝ} (hv : v ≤ 0) (θ : EuclideanSpace ℝ ι) :
    multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)) = Measure.dirac θ := by
  by_cases hS : (v • (1 : Matrix ι ι ℝ)).PosSemidef
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    · rw [Subsingleton.elim (v • (1 : Matrix ι ι ℝ)) 0, multivariateGaussian_zero_right]
    · have h := hS.diag_nonneg (i := i)
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
      rw [le_antisymm hv h, zero_smul, multivariateGaussian_zero_right]
  · exact multivariateGaussian_of_not_posSemidef θ hS

/-- **Stein's identity** for a real function under `N(θ, v I)`, `v ≥ 0`: for a differentiable `f`
such that `f`, `(xᵢ - θᵢ) f` and the partial derivative `∂ᵢ f` are integrable,
`E[(Xᵢ - θᵢ) f(X)] = v E[∂ᵢ f(X)]`. -/
theorem integral_sub_mul_eq_mul_integral_fderiv_multivariateGaussian {v : ℝ} (hv : 0 ≤ v)
    {θ : EuclideanSpace ℝ ι} {f : EuclideanSpace ℝ ι → ℝ} (hf : Differentiable ℝ f) (i : ι)
    (hfi : Integrable f (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ))))
    (hxf : Integrable (fun x ↦ (x i - θ i) * f x)
      (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ))))
    (hdf : Integrable (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1))
      (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)))) :
    ∫ x, (x i - θ i) * f x ∂multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)) =
      v * ∫ x, fderiv ℝ f x (EuclideanSpace.single i 1)
        ∂multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)) := by
  rcases hv.eq_or_lt with rfl | hv
  · simp
  set c : ℝ := (2 * π * v) ^ (-(Fintype.card ι : ℝ) / 2)
  set φ : EuclideanSpace ℝ ι → ℝ := fun x ↦ c * exp (-‖x - θ‖ ^ 2 / (2 * v)) with hφ
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  have hφm : AEMeasurable φ volume := by fun_prop
  have hφnn : 0 ≤ᵐ[volume] φ := ae_of_all _ fun x ↦ by positivity
  have hP := multivariateGaussian_smul_one_eq_withDensity hv θ
  have hint (g : EuclideanSpace ℝ ι → ℝ) :
      Integrable g (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ))) ↔
        Integrable (fun x ↦ φ x * g x) volume := by
    simp only [hP, TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff hφm hφnn, smul_eq_mul,
      φ, c]
  have hφd (x : EuclideanSpace ℝ ι) : HasFDerivAt φ
      (c • ((-2 * (2 * v)⁻¹ * exp (-(2 * v)⁻¹ * ‖x - θ‖ ^ 2)) • innerSL ℝ (x - θ))) x := by
    have he : φ = fun y ↦ c * exp (-(2 * v)⁻¹ * ‖y - θ‖ ^ 2) := by
      funext y
      simp only [hφ, neg_mul, inv_mul_eq_div, neg_div]
    rw [he]
    exact (TauCeti.hasFDerivAt_exp_neg_mul_norm_sub_sq ((2 * v)⁻¹) θ x).const_mul c
  have hφe (x : EuclideanSpace ℝ ι) : fderiv ℝ φ x e = -(v⁻¹ * (x i - θ i)) * φ x := by
    rw [(hφd x).fderiv]
    simp only [e, smul_apply, innerSL_apply_apply, conj_trivial,
      EuclideanSpace.inner_single_right, PiLp.sub_apply, hφ, smul_eq_mul]
    field_simp
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := e)
    (((hint _).1 hxf).const_mul (-v⁻¹) |>.congr (ae_of_all _ fun x ↦ by
      simp only [hφe]; ring))
    ((hint _).1 hdf) ((hint _).1 hfi) (fun x _ ↦ (hφd x).differentiableAt)
    (fun x _ ↦ hf x)
  rw [hP, TauCeti.MeasureTheory.integral_withDensity_ofReal hφm hφnn,
    TauCeti.MeasureTheory.integral_withDensity_ofReal hφm hφnn]
  simp only [smul_eq_mul]
  rw [hibp, ← integral_neg, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [hφe]
  field_simp

/-- **Stein's identity** for `X ~ N(θ, v I)`, `v ≥ 0`, and a differentiable vector field
`g ∈ L²` with integrable diagonal partial derivatives: `E[(Xᵢ - θᵢ) gᵢ(X)] = v E[∂ᵢ gᵢ(X)]`. -/
theorem gaussian_integration_by_parts {v : ℝ} (hv : 0 ≤ v) {θ : EuclideanSpace ℝ ι}
    {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hg : Differentiable ℝ g)
    (hg2 : MemLp g 2 (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)))) (i : ι)
    (hdi : Integrable (fun x ↦ fderiv ℝ g x (EuclideanSpace.single i 1) i)
      (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)))) :
    ∫ x, (x i - θ i) * g x i ∂multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)) =
      v * ∫ x, fderiv ℝ g x (EuclideanSpace.single i 1) i
        ∂multivariateGaussian θ (v • (1 : Matrix ι ι ℝ)) := by
  have hgi : MemLp (fun x ↦ g x i) 2 (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ))) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hg2
  have hxi : MemLp (fun x : EuclideanSpace ℝ ι ↦ x i - θ i) 2
      (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ))) :=
    (IsGaussian.memLp_dual _ (EuclideanSpace.proj i) 2 (by simp)).sub (memLp_const _)
  have hd (x : EuclideanSpace ℝ ι) : fderiv ℝ (fun y ↦ g y i) x (EuclideanSpace.single i 1) =
      fderiv ℝ g x (EuclideanSpace.single i 1) i :=
    congrArg (· (EuclideanSpace.single i 1))
      ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x (hg x).hasFDerivAt).fderiv
  simp_rw [← hd] at hdi ⊢
  exact integral_sub_mul_eq_mul_integral_fderiv_multivariateGaussian hv
    (fun x ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x (hg x)) i
    (hgi.integrable one_le_two) (hxi.integrable_mul hgi) hdi

/-- In dimension at least `3`, the real-valued reciprocal `(‖x‖ ^ 2)⁻¹`, which takes the value `0`
at the origin, is integrable under `multivariateGaussian θ (v I)` for every real `v`. For `v > 0`
this is the usual integrability of `‖x‖⁻²` under `N(θ, v I)`; for `v ≤ 0` the law is the point
mass at `θ` (the fallback value of `multivariateGaussian` when `v < 0`), and when `θ = 0` the
statement relies on the convention `0⁻¹ = 0`. -/
theorem integrable_inv_norm_sq_multivariateGaussian (hι : 3 ≤ Fintype.card ι) (v : ℝ)
    (θ : EuclideanSpace ℝ ι) :
    Integrable (fun x : EuclideanSpace ℝ ι ↦ (‖x‖ ^ 2)⁻¹)
      (multivariateGaussian θ (v • (1 : Matrix ι ι ℝ))) := by
  rcases le_or_gt v 0 with hv | hv
  · rw [multivariateGaussian_smul_one_of_nonpos hv]
    exact integrable_dirac (by simp)
  set c : ℝ := (2 * π * v) ^ (-(Fintype.card ι : ℝ) / 2)
  set φ : EuclideanSpace ℝ ι → ℝ := fun x ↦ c * exp (-‖x - θ‖ ^ 2 / (2 * v))
  have hφm : AEMeasurable φ volume := by fun_prop
  have hφnn (x : EuclideanSpace ℝ ι) : 0 ≤ φ x := by positivity
  have hφle (x : EuclideanSpace ℝ ι) : φ x ≤ c :=
    mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.2 (by positivity)) (by positivity)))
  have hφi : Integrable φ volume :=
    TauCeti.MeasureTheory.integrable_of_eq_withDensity
      (multivariateGaussian_smul_one_eq_withDensity hv θ) hφm (ae_of_all _ hφnn)
  have hball : IntegrableOn (fun x : EuclideanSpace ℝ ι ↦ ‖x‖ ^ (-2 : ℝ)) (Metric.ball 0 1) :=
    TauCeti.integrableOn_norm_rpow_ball (by simp; omega)
  rw [multivariateGaussian_smul_one_eq_withDensity hv θ,
    TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff hφm (ae_of_all _ hφnn)]
  refine Integrable.mono' (((hball.integrable_indicator measurableSet_ball).const_mul c).add
    hφi) (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [smul_eq_mul, Real.norm_of_nonneg (by positivity), Pi.add_apply]
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ ι) 1
  · rw [Set.indicator_of_mem hx, rpow_neg (norm_nonneg _), rpow_two]
    nlinarith [mul_le_mul_of_nonneg_right (hφle x) (inv_nonneg.2 (sq_nonneg ‖x‖)), hφnn x]
  · rw [Set.indicator_of_notMem hx, mul_zero, zero_add]
    have h1 : 1 ≤ ‖x‖ ^ 2 := one_le_pow₀ (by simpa using hx)
    exact mul_le_of_le_one_right (hφnn x) (inv_le_one_of_one_le₀ h1)

end TauCeti.Probability
