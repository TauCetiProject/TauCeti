/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.MixedMoments
public import TauCeti.Probability.Distributions.Gaussian.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.Analysis.Matrix.Sqrt

/-!
# Recursion for Gaussian mixed moments

Gaussian integration by parts reduces a product moment by two factors: choose one centered
factor, pair it with each remaining factor, and multiply the lower moment by their covariance.
Real and complex real-linear observables are allowed. The remaining factors may carry arbitrary
affine shifts, and the positions indexing them need
not be distinct. Empty products and singular positive-semidefinite covariances are allowed.

Iterating the centered recurrence yields the Wick–Isserlis pairing expansion for higher
Gaussian mixed moments. Keeping affine shifts on the remaining factors also supports
noncentered and partially centered products, with matching recurrences for linear observables
of `IsGaussian` measures, coordinates of `multivariateGaussian` laws, and random vectors with
those laws via `HasLaw`.

## Main results

* `TauCeti.Probability.integral_sub_mul_prod_affine_gaussianReal`: the scalar recurrence for
  affine functions of a real Gaussian.
* `TauCeti.Probability.integral_clm_mul_prod_pi_gaussianReal`: the recurrence for affine forms
  of independent standard Gaussians.
* `TauCeti.Probability.integral_sub_mul_prod_add_multivariateGaussian`: the coordinate
  recurrence for a multivariate Gaussian, with centered and zero-mean raw specializations.
* `ProbabilityTheory.IsGaussian.integral_sub_dual_mul_prod_dual`: the recurrence for linear
  observables of a Gaussian measure, with the centered specialization
  `ProbabilityTheory.IsGaussian.integral_sub_dual_mul_prod_sub_dual`.
* `ProbabilityTheory.HasLaw.integral_sub_mul_prod_add_multivariateGaussian`: the coordinate
  recurrence for a random vector with a multivariate Gaussian law, with centered and zero-mean
  raw specializations.

## References

* Scalar Gaussian integration by parts:
  `TauCeti.Probability.integral_sub_mul_eq_mul_integral_deriv_gaussianReal`.
* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134–139.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped MatrixOrder NNReal

namespace TauCeti.Probability

variable {ι κ : Type*} [DecidableEq ι]

/-- Integration by parts for a product of affine functions of a real Gaussian.
Real and complex coefficients are allowed, including zero variance. -/
theorem integral_sub_mul_prod_affine_gaussianReal {𝕜 : Type*} [RCLike 𝕜] (m : ℝ) (v : ℝ≥0)
    (s : Finset ι) (a b : ι → 𝕜) :
    (∫ x, ((x - m : ℝ) : 𝕜) * ∏ i ∈ s, (a i * (x : 𝕜) + b i) ∂gaussianReal m v) =
      ((v : ℝ) : 𝕜) * ∑ i ∈ s, a i *
        ∫ x, ∏ j ∈ s.erase i, (a j * (x : 𝕜) + b j) ∂gaussianReal m v := by
  classical
  let L (i : ι) : ℝ →L[ℝ] 𝕜 := ContinuousLinearMap.toSpanSingleton ℝ (a i)
  have hint (t : Finset ι) :
      Integrable (fun x : ℝ ↦ ∏ i ∈ t, (a i * (x : 𝕜) + b i)) (gaussianReal m v) := by
    simpa [L, RCLike.real_smul_eq_coe_mul, mul_comm] using
      IsGaussian.integrable_prod_clm (gaussianReal m v) t L b
  have hder (x : ℝ) : HasDerivAt (fun x : ℝ ↦ ∏ i ∈ s, (a i * (x : 𝕜) + b i))
      (∑ i ∈ s, a i * ∏ j ∈ s.erase i, (a j * (x : 𝕜) + b j)) x := by
    simpa only [smul_eq_mul, mul_comm, id_eq, mul_one, RCLike.ofRealCLM_apply,
      RCLike.ofReal_one] using HasDerivAt.fun_finsetProd
      (u := s) (fun i _ ↦
        ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasDerivAt.const_mul (a i)).add_const (b i))
  have hdf : deriv (fun x : ℝ ↦ ∏ i ∈ s, (a i * (x : 𝕜) + b i)) =
      fun x : ℝ ↦ ∑ i ∈ s, a i * ∏ j ∈ s.erase i, (a j * (x : 𝕜) + b j) :=
    funext fun x : ℝ ↦ (hder x).deriv
  simp_rw [← RCLike.real_smul_eq_coe_mul]
  rw [integral_sub_smul_eq_smul_integral_deriv_gaussianReal m v _
    (fun x : ℝ ↦ (hder x).differentiableAt)
    (by
      simpa [L, sub_eq_add_neg, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_sub,
        RCLike.algebraMap_eq_ofReal, mul_comm] using
        IsGaussian.integrable_clm_add_mul_prod (gaussianReal m v) s
          (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) (-(m : 𝕜)) L b)
    (by rw [hdf]; exact integrable_finsetSum s fun i _ ↦ (hint _).const_mul _), hdf,
    integral_finsetSum _ (fun i _ ↦ (hint _).const_mul _)]
  simp_rw [integral_const_mul]

section Product

variable [Fintype κ] [DecidableEq κ] {𝕜 : Type*} [RCLike 𝕜]

/-- Integration by parts in one coordinate of a finite product of standard Gaussians,
with a product of real or complex affine test functions. -/
theorem integral_eval_mul_prod_pi_gaussianReal (s : Finset ι)
    (L : ι → (κ → ℝ) →L[ℝ] 𝕜) (c : ι → 𝕜) (k : κ) :
    (∫ x, (x k : 𝕜) * ∏ i ∈ s, (L i x + c i) ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) =
      ∑ i ∈ s, L i (Pi.single k 1) *
        ∫ x, ∏ j ∈ s.erase i, (L j x + c j) ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : κ ↦ gaussianReal 0 1)
  have hint (t : Finset ι) : Integrable (fun x ↦ ∏ i ∈ t, (L i x + c i)) μ :=
    IsGaussian.integrable_prod_clm μ t L c
  have hfull : Integrable (fun x ↦ (x k : 𝕜) * ∏ i ∈ s, (L i x + c i)) μ := by
    simpa using IsGaussian.integrable_clm_add_mul_prod μ s
      (RCLike.ofRealCLM.comp (ContinuousLinearMap.proj k)) 0 L c
  -- Resampling one coordinate makes each affine form affine in the new scalar value.
  have hslice (i : ι) (x : κ → ℝ) (y : ℝ) :
      L i (Function.update x k y) + c i =
        L i (Pi.single k 1) * (y : 𝕜) + (L i (x - Pi.single k (x k)) + c i) := by
    rw [Pi.update_eq_sub_add_single, map_add]
    have hs : Pi.single k y = y • Pi.single k (1 : ℝ) := by
      simpa using Pi.single_smul (f := fun _ : κ ↦ ℝ) k y (1 : ℝ)
    rw [hs, map_smul, RCLike.real_smul_eq_coe_mul]
    ring
  have hslices (t : Finset ι) : Integrable
      (fun x ↦ ∫ y, ∏ i ∈ t, (L i (Function.update x k y) + c i) ∂gaussianReal 0 1) μ :=
    Integrable.integral_prod_left <|
      (measurePreserving_update_prod_pi (fun _ : κ ↦ gaussianReal 0 1) k)
        |>.integrable_comp_of_integrable (hint t)
  -- Apply the scalar identity on each slice, then restore the product measure.
  calc
    _ = ∫ x, ∫ y, (y : 𝕜) * ∏ i ∈ s, (L i (Function.update x k y) + c i)
        ∂gaussianReal 0 1 ∂μ := by
      simpa using (integral_integral_update_pi (fun _ : κ ↦ gaussianReal 0 1) k hfull).symm
    _ = ∫ x, ∑ i ∈ s, L i (Pi.single k 1) *
        ∫ y, ∏ j ∈ s.erase i, (L j (Function.update x k y) + c j) ∂gaussianReal 0 1 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp_rw [hslice]
      simpa only [sub_zero, NNReal.coe_one, RCLike.ofReal_one, one_mul] using
        integral_sub_mul_prod_affine_gaussianReal 0 1 s
          (fun i ↦ L i (Pi.single k 1)) (fun i ↦ L i (x - Pi.single k (x k)) + c i)
    _ = ∑ i ∈ s, L i (Pi.single k 1) *
        ∫ x, ∫ y, ∏ j ∈ s.erase i, (L j (Function.update x k y) + c j)
          ∂gaussianReal 0 1 ∂μ := by
      rw [integral_finsetSum _ (fun i _ ↦ (hslices _).const_mul _)]
      simp_rw [integral_const_mul]
    _ = _ := by
      apply sum_congr rfl
      intro i _
      congr 1
      exact integral_integral_update_pi (fun _ : κ ↦ gaussianReal 0 1) k (hint (s.erase i))

/-- A product moment of affine forms of independent standard Gaussians reduces by pairing
one distinguished linear form with each remaining form. The coefficient is the Euclidean
bilinear pairing of their coefficient vectors, without conjugation in the complex case. -/
theorem integral_clm_mul_prod_pi_gaussianReal (s : Finset ι)
    (L₀ : (κ → ℝ) →L[ℝ] 𝕜) (L : ι → (κ → ℝ) →L[ℝ] 𝕜) (c : ι → 𝕜) :
    (∫ x, L₀ x * ∏ i ∈ s, (L i x + c i) ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) =
      ∑ i ∈ s, (∑ k, L₀ (Pi.single k 1) * L i (Pi.single k 1)) *
        ∫ x, ∏ j ∈ s.erase i, (L j x + c j) ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
  have hlin (x : κ → ℝ) : L₀ x = ∑ k, L₀ (Pi.single k 1) * (x k : 𝕜) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp only [map_sum]
    apply sum_congr rfl
    intro k _
    have hs : Pi.single k (x k) = x k • Pi.single k (1 : ℝ) := by
      simpa using Pi.single_smul (f := fun _ : κ ↦ ℝ) k (x k) (1 : ℝ)
    simp [hs, RCLike.real_smul_eq_coe_mul, mul_comm]
  have hint (k : κ) : Integrable (fun x ↦ (x k : 𝕜) * ∏ i ∈ s, (L i x + c i))
      (Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) := by
    simpa using IsGaussian.integrable_clm_add_mul_prod _ s
      (RCLike.ofRealCLM.comp (ContinuousLinearMap.proj k)) 0 L c
  have hfun : (fun x ↦ L₀ x * ∏ i ∈ s, (L i x + c i)) =
      fun x ↦ ∑ k, L₀ (Pi.single k 1) * ((x k : 𝕜) * ∏ i ∈ s, (L i x + c i)) := by
    funext x
    rw [hlin x, sum_mul]
    simp only [mul_assoc]
  rw [hfun]
  rw [integral_finsetSum _ (fun k _ ↦ (hint k).const_mul _)]
  simp_rw [integral_const_mul, integral_eval_mul_prod_pi_gaussianReal,
    mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp_rw [sum_mul]

end Product

section Multivariate

variable [Fintype κ] [DecidableEq κ]

/-- The multivariate Gaussian moment recursion. Pair the centered distinguished coordinate
with every remaining affinely shifted position and take the moment of the factors left over.
Positions may refer to repeated coordinates, and the covariance may be singular. -/
theorem integral_sub_mul_prod_add_multivariateGaussian (m : EuclideanSpace ℝ κ)
    {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (s : Finset ι) (f : ι → κ) (c : ι → ℝ) (k : κ) :
    (∫ x, (x k - m k) * ∏ i ∈ s, (x (f i) + c i) ∂multivariateGaussian m S) =
      ∑ i ∈ s, S k (f i) *
        ∫ x, ∏ j ∈ s.erase i, (x (f j) + c j) ∂multivariateGaussian m S := by
  let T : (κ → ℝ) →L[ℝ] EuclideanSpace ℝ κ :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).comp
      (EuclideanSpace.equiv κ ℝ).symm.toContinuousLinearMap
  let L (i : κ) : StrongDual ℝ (κ → ℝ) := (EuclideanSpace.proj i).comp T
  have hT (j i : κ) : T (Pi.single j 1) i = CFC.sqrt S i j := by
    simp [T]
  have hcoeff (i : ι) : (∑ j, L k (Pi.single j 1) * L (f i) (Pi.single j 1)) =
      S k (f i) := by
    simpa only [L, ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj, hT,
      Matrix.mul_apply, Matrix.transpose_apply] using
      congrArg (fun A : Matrix κ κ ℝ ↦ A k (f i)) hS.sqrt_mul_transpose_sqrt
  -- The law is the image of the standard Gaussian product under `y ↦ m + T y`.
  have hmap : (Measure.pi (fun _ : κ ↦ gaussianReal 0 1)).map (fun y ↦ m + T y) =
      multivariateGaussian m S := by
    simpa only [T, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using
      (multivariateGaussian_eq_map_pi m S).symm
  have hcoord (y : κ → ℝ) (i : κ) : (m + T y) i = L i y + m i := by
    simp only [L, ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj, PiLp.add_apply,
      add_comm]
  have h := integral_clm_mul_prod_pi_gaussianReal s (L k) (fun i ↦ L (f i))
    (fun i ↦ m (f i) + c i)
  simp only [hcoeff] at h
  calc
    _ = ∫ y, L k y * ∏ i ∈ s, (L (f i) y + (m (f i) + c i))
        ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
      rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
      simp only [hcoord, add_sub_cancel_right, add_assoc]
    _ = _ := by
      rw [h]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
      simp only [hcoord, add_assoc]

/-- The centered mixed-moment recursion at an arbitrary Gaussian mean. Each covariance
contracts two factors, leaving a centered moment of degree two less. -/
theorem integral_sub_mul_prod_sub_multivariateGaussian (m : EuclideanSpace ℝ κ)
    {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (s : Finset ι) (f : ι → κ) (k : κ) :
    (∫ x, (x k - m k) * ∏ i ∈ s, (x (f i) - m (f i)) ∂multivariateGaussian m S) =
      ∑ i ∈ s, S k (f i) *
        ∫ x, ∏ j ∈ s.erase i, (x (f j) - m (f j)) ∂multivariateGaussian m S := by
  simpa only [sub_eq_add_neg] using
    integral_sub_mul_prod_add_multivariateGaussian m hS s f (fun i ↦ -m (f i)) k

/-- The centered multivariate Gaussian moment recursion for raw coordinate products. -/
theorem integral_eval_mul_prod_multivariateGaussian {S : Matrix κ κ ℝ} (hS : S.PosSemidef)
    (s : Finset ι) (f : ι → κ) (k : κ) :
    (∫ x, x k * ∏ i ∈ s, x (f i) ∂multivariateGaussian 0 S) =
      ∑ i ∈ s, S k (f i) *
        ∫ x, ∏ j ∈ s.erase i, x (f j) ∂multivariateGaussian 0 S := by
  simpa using integral_sub_mul_prod_add_multivariateGaussian 0 hS s f 0 k

/-- The centered Gaussian moment recursion for real or complex real-linear observables.
The contraction coefficients are bilinear second moments, without complex conjugation.
No nondegeneracy or covariance-validity hypothesis is required. -/
theorem integral_clm_mul_prod_sub_multivariateGaussian {𝕜 : Type*} [RCLike 𝕜]
    (m : EuclideanSpace ℝ κ) (S : Matrix κ κ ℝ) (s : Finset ι)
    (L₀ : EuclideanSpace ℝ κ →L[ℝ] 𝕜) (L : ι → EuclideanSpace ℝ κ →L[ℝ] 𝕜) :
    (∫ x, L₀ (x - m) * ∏ i ∈ s, L i (x - m) ∂multivariateGaussian m S) =
      ∑ i ∈ s, (∫ x, L₀ (x - m) * L i (x - m) ∂multivariateGaussian m S) *
        ∫ x, ∏ j ∈ s.erase i, L j (x - m) ∂multivariateGaussian m S := by
  let T : (κ → ℝ) →L[ℝ] EuclideanSpace ℝ κ :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).comp
      (EuclideanSpace.equiv κ ℝ).symm.toContinuousLinearMap
  have hpush (f : EuclideanSpace ℝ κ → 𝕜) (hf : Continuous f) :
      ∫ x, f (x - m) ∂multivariateGaussian m S =
        ∫ y, f (T y) ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
    rw [multivariateGaussian_eq_map_pi, integral_map (by fun_prop) (by fun_prop)]
    simp only [add_sub_cancel_left, T, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
  have hprod (t : Finset ι) := hpush (fun x ↦ ∏ i ∈ t, L i x) (by fun_prop)
  have hpair (i : ι) :
      (∫ y, L₀ (T y) * L i (T y) ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) =
        ∑ k, L₀ (T (Pi.single k 1)) * L i (T (Pi.single k 1)) := by
    simpa using integral_clm_mul_prod_pi_gaussianReal ({i} : Finset ι)
      (L₀.comp T) (fun j ↦ (L j).comp T) 0
  rw [hpush (fun x ↦ L₀ x * ∏ i ∈ s, L i x) (by fun_prop)]
  have hpair' (i : ι) := hpush (fun x ↦ L₀ x * L i x) (by fun_prop)
  simp_rw [hpair', hpair, hprod]
  simpa using integral_clm_mul_prod_pi_gaussianReal s (L₀.comp T)
    (fun j ↦ (L j).comp T) 0

end Multivariate

end TauCeti.Probability

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Gaussian moment recursion for linear observables. A centered observable times a finite
product of affine observables reduces by pairing it with each factor through their covariance.
The observables may be repeated or correlated, and no nondegeneracy is assumed. -/
theorem integral_sub_dual_mul_prod_dual (μ : Measure E) [IsGaussian μ]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (L₀ : StrongDual ℝ E)
    (L : ι → StrongDual ℝ E) (c : ι → ℝ) :
    (∫ x, (L₀ x - μ[L₀]) * ∏ i ∈ s, (L i x + c i) ∂μ) =
      ∑ i ∈ s, cov[L₀, L i; μ] * ∫ x, ∏ j ∈ s.erase i, (L j x + c j) ∂μ := by
  classical
  -- Push `μ` forward to the joint law of `L₀` and of the observables indexed by `s`.
  let F : Option s → StrongDual ℝ E := fun a ↦ a.elim L₀ fun i ↦ L i
  let T : E →L[ℝ] EuclideanSpace ℝ (Option s) :=
    (EuclideanSpace.equiv (Option s) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi F)
  have hT (x : E) (a : Option s) : T x a = F a x := by
    simp [T]
  have hpush (g : EuclideanSpace ℝ (Option s) → ℝ) (hg : Continuous g) :
      ∫ y, g y ∂μ.map T = ∫ x, g (T x) ∂μ :=
    integral_map (by fun_prop) hg.aestronglyMeasurable
  have hmean : (∫ y, y ∂μ.map T) none = μ[L₀] := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) (none : Option s)).integral_comp_comm
      (IsGaussian.integrable_id (μ := μ.map T))
    simp only [EuclideanSpace.coe_proj, id_eq] at h
    rw [← h, hpush _ (by fun_prop)]
    simp [hT, F]
  have hcomp (a : Option s) : (fun y : EuclideanSpace ℝ (Option s) ↦ y a) ∘ T = F a :=
    funext fun x ↦ by simp only [Function.comp_apply, hT]
  have hcov (i : s) : TauCeti.covMatrix (μ.map T) none (some i) = cov[L₀, L i; μ] := by
    rw [TauCeti.covMatrix_apply, covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
    simp only [hcomp, F, Option.elim_none, Option.elim_some]
  -- The pushed-forward law is the multivariate Gaussian with its own mean and covariance.
  have h := TauCeti.Probability.integral_sub_mul_prod_add_multivariateGaussian
    (∫ y, y ∂μ.map T) (TauCeti.posSemidef_covMatrix (μ.map T) IsGaussian.memLp_two_id)
    (univ : Finset s) some (fun i ↦ c i) none
  rw [← TauCeti.Probability.eq_multivariateGaussian_covMatrix (μ.map T)] at h
  calc
    _ = ∫ y, (y none - (∫ z, z ∂μ.map T) none) * ∏ i : s, (y (some i) + c i) ∂μ.map T := by
      rw [hpush _ (by fun_prop), hmean]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp only [hT, F, Option.elim_none, Option.elim_some, Finset.univ_eq_attach]
      rw [Finset.prod_attach s fun i ↦ L i x + c i]
    _ = _ := h
    _ = _ := by
      rw [← Finset.sum_coe_sort s]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [hcov, hpush _ (by fun_prop)]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simpa [hT, F, Finset.univ_eq_attach] using
        Finset.prod_erase_attach (fun j ↦ L j x + c j) i

/-- The centered Gaussian moment recursion for linear observables. Each covariance contracts
the distinguished observable with one remaining factor, leaving a centered moment of degree two
less. -/
theorem integral_sub_dual_mul_prod_sub_dual (μ : Measure E) [IsGaussian μ]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (L₀ : StrongDual ℝ E)
    (L : ι → StrongDual ℝ E) :
    (∫ x, (L₀ x - μ[L₀]) * ∏ i ∈ s, (L i x - μ[L i]) ∂μ) =
      ∑ i ∈ s, cov[L₀, L i; μ] * ∫ x, ∏ j ∈ s.erase i, (L j x - μ[L j]) ∂μ := by
  simpa only [sub_eq_add_neg] using
    integral_sub_dual_mul_prod_dual μ s L₀ L fun i ↦ -μ[L i]

end ProbabilityTheory.IsGaussian

namespace ProbabilityTheory.HasLaw

variable {ι κ Ω : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ κ}
  {m : EuclideanSpace ℝ κ} {S : Matrix κ κ ℝ}

/-- The mixed-moment recursion for a random vector with a multivariate Gaussian law, with
affinely shifted remaining factors. Neither independence of coordinates nor nondegeneracy is
required. -/
theorem integral_sub_mul_prod_add_multivariateGaussian
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosSemidef)
    (s : Finset ι) (f : ι → κ) (c : ι → ℝ) (k : κ) :
    (∫ ω, (X ω k - m k) * ∏ i ∈ s, (X ω (f i) + c i) ∂P) =
      ∑ i ∈ s, S k (f i) * ∫ ω, ∏ j ∈ s.erase i, (X ω (f j) + c j) ∂P := by
  have hprod (t : Finset ι) :
      (∫ ω, ∏ i ∈ t, (X ω (f i) + c i) ∂P) =
        ∫ x, ∏ i ∈ t, (x (f i) + c i) ∂multivariateGaussian m S :=
    hX.integral_comp (f := fun x : EuclideanSpace ℝ κ ↦
      ∏ i ∈ t, (x (f i) + c i)) (by fun_prop)
  simp_rw [hprod]
  calc
    _ = ∫ x, (x k - m k) * ∏ i ∈ s, (x (f i) + c i)
        ∂multivariateGaussian m S := hX.integral_comp (by fun_prop)
    _ = _ := TauCeti.Probability.integral_sub_mul_prod_add_multivariateGaussian m hS s f c k

/-- The centered mixed-moment recursion for a random vector with a multivariate Gaussian law.
Neither independence of coordinates nor nondegeneracy is required. -/
theorem integral_sub_mul_prod_sub_multivariateGaussian
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosSemidef)
    (s : Finset ι) (f : ι → κ) (k : κ) :
    (∫ ω, (X ω k - m k) * ∏ i ∈ s, (X ω (f i) - m (f i)) ∂P) =
      ∑ i ∈ s, S k (f i) *
        ∫ ω, ∏ j ∈ s.erase i, (X ω (f j) - m (f j)) ∂P := by
  simpa only [sub_eq_add_neg] using
    hX.integral_sub_mul_prod_add_multivariateGaussian hS s f (fun i ↦ -m (f i)) k

/-- The moment recursion for raw coordinate products of a random vector with a centered
multivariate Gaussian law. -/
theorem integral_eval_mul_prod_multivariateGaussian
    (hX : HasLaw X (multivariateGaussian 0 S) P) (hS : S.PosSemidef)
    (s : Finset ι) (f : ι → κ) (k : κ) :
    (∫ ω, X ω k * ∏ i ∈ s, X ω (f i) ∂P) =
      ∑ i ∈ s, S k (f i) * ∫ ω, ∏ j ∈ s.erase i, X ω (f j) ∂P := by
  simpa using hX.integral_sub_mul_prod_add_multivariateGaussian hS s f 0 k

end ProbabilityTheory.HasLaw
