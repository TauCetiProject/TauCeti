/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.MixedMoments
public import TauCeti.Probability.Distributions.Gaussian.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts.Basic
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Recursion for Gaussian mixed moments

Gaussian integration by parts reduces a product moment by two factors: choose one centered
factor, pair it with each remaining factor, and multiply by the moment of the remaining product.
For real observables the pairing is covariance; for complex real-linear observables it is the
unconjugated bilinear centered second moment. The remaining factors may carry arbitrary affine
shifts and may repeat. Empty products and singular covariance matrices are allowed.

Real or complex real-linear recurrences are provided for `gaussianReal`, products of standard
real Gaussians, `multivariateGaussian`, and arbitrary `IsGaussian` measures. The `HasLaw`
coordinate recurrences are real-valued. Iterating the centered recurrence yields the
Wick–Isserlis pairing expansion, while affine shifts support noncentered and partially centered
products.

## Main results

* `TauCeti.Probability.integral_sub_mul_prod_affine_gaussianReal`: the scalar recurrence for
  affine functions of a real Gaussian.
* `TauCeti.Probability.integral_clm_mul_prod_pi_gaussianReal`: the recurrence for affine forms
  of independent standard Gaussians.
* `TauCeti.Probability.integral_clm_sub_mul_prod_add_multivariateGaussian`: the affine real-linear
  observable recurrence, with centered specialization
  `TauCeti.Probability.integral_clm_sub_mul_prod_sub_multivariateGaussian`.
* `TauCeti.Probability.integral_sub_mul_prod_add_multivariateGaussian`: the real coordinate
  recurrence for a multivariate Gaussian, with centered and zero-mean raw specializations.
* `ProbabilityTheory.IsGaussian.integral_sub_clm_mul_prod_clm`: the recurrence for linear
  observables of a Gaussian measure, with the centered specialization
  `ProbabilityTheory.IsGaussian.integral_sub_clm_mul_prod_sub_clm`.
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

/-- The Gaussian moment recursion for real or complex real-linear observables, with
arbitrary affine shifts on the remaining factors. The contraction coefficients are bilinear
second moments, without complex conjugation. No covariance-validity hypothesis is required. -/
theorem integral_clm_sub_mul_prod_add_multivariateGaussian {𝕜 : Type*} [RCLike 𝕜]
    (m : EuclideanSpace ℝ κ) (S : Matrix κ κ ℝ) (s : Finset ι)
    (L₀ : EuclideanSpace ℝ κ →L[ℝ] 𝕜) (L : ι → EuclideanSpace ℝ κ →L[ℝ] 𝕜) (c : ι → 𝕜) :
    (∫ x, L₀ (x - m) * ∏ i ∈ s, (L i x + c i) ∂multivariateGaussian m S) =
      ∑ i ∈ s, (∫ x, L₀ (x - m) * L i (x - m) ∂multivariateGaussian m S) *
        ∫ x, ∏ j ∈ s.erase i, (L j x + c j) ∂multivariateGaussian m S := by
  let T : (κ → ℝ) →L[ℝ] EuclideanSpace ℝ κ :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).comp
      (EuclideanSpace.equiv κ ℝ).symm.toContinuousLinearMap
  have hpush (f : EuclideanSpace ℝ κ → 𝕜) (hf : Continuous f) :
      ∫ x, f x ∂multivariateGaussian m S =
        ∫ y, f (m + T y) ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
    rw [multivariateGaussian_eq_map_pi, integral_map (by fun_prop) (by fun_prop)]
    simp only [T, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  have hprod (t : Finset ι) :
      (∫ x, ∏ i ∈ t, (L i x + c i) ∂multivariateGaussian m S) =
        ∫ y, ∏ i ∈ t, ((L i).comp T y + (L i m + c i))
          ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
    rw [hpush _ (by fun_prop)]
    simp only [map_add, ContinuousLinearMap.comp_apply, add_left_comm, add_assoc]
  have hpair (i : ι) :
      (∫ x, L₀ (x - m) * L i (x - m) ∂multivariateGaussian m S) =
        ∑ k, L₀ (T (Pi.single k 1)) * L i (T (Pi.single k 1)) := by
    rw [hpush _ (by fun_prop)]
    simpa [ContinuousLinearMap.comp_apply] using
      integral_clm_mul_prod_pi_gaussianReal ({i} : Finset ι)
        (L₀.comp T) (fun j ↦ (L j).comp T) 0
  rw [hpush _ (by fun_prop)]
  simp_rw [hpair, hprod]
  simpa only [add_sub_cancel_left, map_add, ContinuousLinearMap.comp_apply,
    add_left_comm, add_assoc] using integral_clm_mul_prod_pi_gaussianReal s
      (L₀.comp T) (fun j ↦ (L j).comp T) (fun j ↦ L j m + c j)

/-- The multivariate Gaussian moment recursion. Pair the centered distinguished coordinate
with every remaining affinely shifted position and take the moment of the factors left over.
Positions may refer to repeated coordinates, and the covariance may be singular. -/
theorem integral_sub_mul_prod_add_multivariateGaussian (m : EuclideanSpace ℝ κ)
    {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (s : Finset ι) (f : ι → κ) (c : ι → ℝ) (k : κ) :
    (∫ x, (x k - m k) * ∏ i ∈ s, (x (f i) + c i) ∂multivariateGaussian m S) =
      ∑ i ∈ s, S k (f i) *
        ∫ x, ∏ j ∈ s.erase i, (x (f j) + c j) ∂multivariateGaussian m S := by
  have hcoeff (i : ι) :
      (∫ x, (x k - m k) * (x (f i) - m (f i)) ∂multivariateGaussian m S) =
        S k (f i) := by
    simpa [covariance] using covariance_eval_multivariateGaussian (μ := m) hS k (f i)
  simpa only [EuclideanSpace.coe_proj, PiLp.sub_apply, hcoeff] using
    integral_clm_sub_mul_prod_add_multivariateGaussian m S s (EuclideanSpace.proj k)
      (fun i ↦ EuclideanSpace.proj (f i)) c

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
theorem integral_clm_sub_mul_prod_sub_multivariateGaussian {𝕜 : Type*} [RCLike 𝕜]
    (m : EuclideanSpace ℝ κ) (S : Matrix κ κ ℝ) (s : Finset ι)
    (L₀ : EuclideanSpace ℝ κ →L[ℝ] 𝕜) (L : ι → EuclideanSpace ℝ κ →L[ℝ] 𝕜) :
    (∫ x, L₀ (x - m) * ∏ i ∈ s, L i (x - m) ∂multivariateGaussian m S) =
      ∑ i ∈ s, (∫ x, L₀ (x - m) * L i (x - m) ∂multivariateGaussian m S) *
        ∫ x, ∏ j ∈ s.erase i, L j (x - m) ∂multivariateGaussian m S := by
  simpa only [← sub_eq_add_neg, map_sub] using
    integral_clm_sub_mul_prod_add_multivariateGaussian m S s L₀ L (fun i ↦ -L i m)

end Multivariate

end TauCeti.Probability

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Gaussian moment recursion for real or complex real-linear observables. A centered
observable times a product of affine observables reduces by pairing it with each factor.
The pairings are bilinear centered second moments, without complex conjugation. -/
theorem integral_sub_clm_mul_prod_clm (μ : Measure E) [IsGaussian μ]
    {ι 𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι] (s : Finset ι) (L₀ : E →L[ℝ] 𝕜)
    (L : ι → E →L[ℝ] 𝕜) (c : ι → 𝕜) :
    (∫ x, (L₀ x - μ[L₀]) * ∏ i ∈ s, (L i x + c i) ∂μ) =
      ∑ i ∈ s, (∫ x, (L₀ x - μ[L₀]) * (L i x - μ[L i]) ∂μ) *
        ∫ x, ∏ j ∈ s.erase i, (L j x + c j) ∂μ := by
  classical
  -- Realify the finite family, then reconstruct its real or complex values linearly.
  let F : Option s → E →L[ℝ] 𝕜 := fun a ↦ a.elim L₀ fun i ↦ L i
  let T : E →L[ℝ] EuclideanSpace ℝ (Option s × Bool) :=
    (EuclideanSpace.equiv (Option s × Bool) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a ↦
        (if a.2 then RCLike.imCLM else RCLike.reCLM).comp (F a.1))
  let G (a : Option s) : EuclideanSpace ℝ (Option s × Bool) →L[ℝ] 𝕜 :=
    RCLike.ofRealCLM.comp (EuclideanSpace.proj (a, false)) +
      (RCLike.I : 𝕜) • RCLike.ofRealCLM.comp (EuclideanSpace.proj (a, true))
  have hG (x : E) (a : Option s) : G a (T x) = F a x := by
    simpa [G, T, mul_comm] using RCLike.re_add_im (F a x)
  have hpush (g : EuclideanSpace ℝ (Option s × Bool) → 𝕜) (hg : Continuous g) :
      ∫ y, g y ∂μ.map T = ∫ x, g (T x) ∂μ :=
    integral_map (by fun_prop) hg.aestronglyMeasurable
  have hmean (a : Option s) : G a (∫ y, y ∂μ.map T) = μ[F a] := by
    have h := (G a).integral_comp_comm (IsGaussian.integrable_id (μ := μ.map T))
    simp only [id_eq] at h
    rw [← h, hpush _ (by fun_prop)]
    simp only [hG]
  have h := TauCeti.Probability.integral_clm_sub_mul_prod_add_multivariateGaussian
    (∫ y, y ∂μ.map T) (TauCeti.covMatrix (μ.map T))
    (univ : Finset s) (G none) (fun i ↦ G (some i)) (fun i ↦ c i)
  rw [← TauCeti.Probability.eq_multivariateGaussian_covMatrix (μ.map T)] at h
  simp_rw [map_sub, hmean] at h
  simp (disch := fun_prop) only [hpush] at h
  simp only [hG] at h
  simp only [F, Option.elim_none, Option.elim_some] at h
  have hprod (x : E) := Finset.prod_attach s (fun i ↦ L i x + c i)
  have herase (x : E) (i : s) := Finset.prod_erase_attach (fun j ↦ L j x + c j) i
  rw [← Finset.sum_coe_sort s]
  simpa only [univ_eq_attach, hprod, herase] using h

/-- The centered Gaussian moment recursion for real or complex real-linear observables.
Each bilinear second moment contracts two factors, leaving a centered moment of degree two less. -/
theorem integral_sub_clm_mul_prod_sub_clm (μ : Measure E) [IsGaussian μ]
    {ι 𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι] (s : Finset ι) (L₀ : E →L[ℝ] 𝕜)
    (L : ι → E →L[ℝ] 𝕜) :
    (∫ x, (L₀ x - μ[L₀]) * ∏ i ∈ s, (L i x - μ[L i]) ∂μ) =
      ∑ i ∈ s, (∫ x, (L₀ x - μ[L₀]) * (L i x - μ[L i]) ∂μ) *
        ∫ x, ∏ j ∈ s.erase i, (L j x - μ[L j]) ∂μ := by
  simpa only [sub_eq_add_neg] using
    integral_sub_clm_mul_prod_clm μ s L₀ L fun i ↦ -μ[L i]

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
