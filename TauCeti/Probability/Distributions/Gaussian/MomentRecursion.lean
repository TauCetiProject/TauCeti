/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.MixedMoments
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.Analysis.Matrix.Sqrt

/-!
# Recursion for Gaussian mixed moments

Gaussian integration by parts reduces a product moment by two factors: choose one centered
factor, pair it with each remaining factor, and multiply the lower moment by their covariance.
The positions indexing the factors need not be distinct coordinates. Empty products and singular
positive-semidefinite covariances are allowed.

The scalar step uses `integral_sub_mul_eq_mul_integral_deriv_gaussianReal`; coordinatewise
Fubini and the covariance square-root representation give the multivariate results.
The imported `ProbabilityTheory.IsGaussian.integrable_prod_dual` supplies integrability of the
finite products appearing in these identities.

## References

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
The identity includes zero variance. -/
theorem integral_sub_mul_prod_affine_gaussianReal (m : ℝ) (v : ℝ≥0)
    (s : Finset ι) (a b : ι → ℝ) :
    (∫ x, (x - m) * ∏ i ∈ s, (a i * x + b i) ∂gaussianReal m v) =
      (v : ℝ) * ∑ i ∈ s, a i * ∫ x, ∏ j ∈ s.erase i, (a j * x + b j) ∂gaussianReal m v := by
  classical
  let L (i : ι) : StrongDual ℝ ℝ := a i • ContinuousLinearMap.id ℝ ℝ
  have hint (t : Finset ι) :
      Integrable (fun x ↦ ∏ i ∈ t, (a i * x + b i)) (gaussianReal m v) := by
    simpa [L] using IsGaussian.integrable_prod_dual (gaussianReal m v) t L b
  have hder (x : ℝ) : HasDerivAt (fun x ↦ ∏ i ∈ s, (a i * x + b i))
      (∑ i ∈ s, a i * ∏ j ∈ s.erase i, (a j * x + b j)) x := by
    simpa only [smul_eq_mul, mul_comm, id_eq, mul_one] using HasDerivAt.fun_finsetProd
      (u := s) (fun i _ ↦ ((hasDerivAt_id x).const_mul (a i)).add_const (b i))
  have hdf : deriv (fun x ↦ ∏ i ∈ s, (a i * x + b i)) =
      fun x ↦ ∑ i ∈ s, a i * ∏ j ∈ s.erase i, (a j * x + b j) :=
    funext fun x ↦ (hder x).deriv
  rw [integral_sub_mul_eq_mul_integral_deriv_gaussianReal m v _
    (fun x ↦ (hder x).differentiableAt)
    (by
      simpa [L, Finset.prod_image, sub_eq_add_neg] using
        IsGaussian.integrable_prod_dual (gaussianReal m v) (insert none (s.image some))
        (fun i ↦ i.elim (ContinuousLinearMap.id ℝ ℝ) L) (fun i ↦ i.elim (-m) b))
    (by rw [hdf]; exact integrable_finsetSum s fun i _ ↦ (hint _).const_mul _), hdf,
    integral_finsetSum _ (fun i _ ↦ (hint _).const_mul _)]
  simp_rw [integral_const_mul]

section Product

variable [Fintype κ] [DecidableEq κ]

/-- Integration by parts in one coordinate of a finite product of standard Gaussians,
with a product of linear test functions. -/
theorem integral_eval_mul_prod_pi_gaussianReal (s : Finset ι)
    (L : ι → StrongDual ℝ (κ → ℝ)) (k : κ) :
    (∫ x, x k * ∏ i ∈ s, L i x ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) =
      ∑ i ∈ s, L i (Pi.single k 1) *
        ∫ x, ∏ j ∈ s.erase i, L j x ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : κ ↦ gaussianReal 0 1)
  have : IsGaussian μ := by
    apply (isGaussian_map_equiv_iff (EuclideanSpace.equiv κ ℝ).symm).mp
    -- The inverse coordinate equivalence is the canonical map into Euclidean space.
    convert (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ κ))) using 1
    exact map_pi_eq_stdGaussian
  have hint (t : Finset ι) : Integrable (fun x ↦ ∏ i ∈ t, L i x) μ := by
    simpa using IsGaussian.integrable_prod_dual μ t L (fun _ ↦ 0)
  have hfull : Integrable (fun x ↦ x k * ∏ i ∈ s, L i x) μ := by
    simpa [Finset.prod_image] using IsGaussian.integrable_prod_dual μ
      (insert none (s.image some))
      (fun i ↦ i.elim (ContinuousLinearMap.proj k) L) (fun _ ↦ 0)
  -- Resampling one coordinate makes each linear form affine in the new scalar value.
  have hslice (i : ι) (x : κ → ℝ) (y : ℝ) :
      L i (Function.update x k y) =
        L i (Pi.single k 1) * y + L i (x - Pi.single k (x k)) := by
    rw [Pi.update_eq_sub_add_single, map_add]
    have hs : Pi.single k y = y • Pi.single k (1 : ℝ) := by
      simpa using Pi.single_smul (f := fun _ : κ ↦ ℝ) k y (1 : ℝ)
    rw [hs, map_smul]
    simp [mul_comm, add_comm]
  have hslices (t : Finset ι) : Integrable
      (fun x ↦ ∫ y, ∏ i ∈ t, L i (Function.update x k y) ∂gaussianReal 0 1) μ :=
    Integrable.integral_prod_left <|
      (measurePreserving_update_prod_pi (fun _ : κ ↦ gaussianReal 0 1) k)
        |>.integrable_comp_of_integrable (hint t)
  -- Apply the scalar identity on each slice, then restore the product measure.
  calc
    _ = ∫ x, ∫ y, y * ∏ i ∈ s, L i (Function.update x k y)
        ∂gaussianReal 0 1 ∂μ := by
      simpa using (integral_integral_update_pi (fun _ : κ ↦ gaussianReal 0 1) k hfull).symm
    _ = ∫ x, ∑ i ∈ s, L i (Pi.single k 1) *
        ∫ y, ∏ j ∈ s.erase i, L j (Function.update x k y) ∂gaussianReal 0 1 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp_rw [hslice]
      simpa using integral_sub_mul_prod_affine_gaussianReal 0 1 s _ _
    _ = ∑ i ∈ s, L i (Pi.single k 1) *
        ∫ x, ∫ y, ∏ j ∈ s.erase i, L j (Function.update x k y)
          ∂gaussianReal 0 1 ∂μ := by
      rw [integral_finsetSum _ (fun i _ ↦ (hslices _).const_mul _)]
      simp_rw [integral_const_mul]
    _ = _ := by
      apply sum_congr rfl
      intro i _
      congr 1
      exact integral_integral_update_pi (fun _ : κ ↦ gaussianReal 0 1) k (hint (s.erase i))

/-- A product moment of linear forms of independent standard Gaussians reduces by pairing
one distinguished form with each remaining form. The coefficient is the Euclidean pairing
of their coefficient vectors. -/
theorem integral_dual_mul_prod_pi_gaussianReal (s : Finset ι)
    (L₀ : StrongDual ℝ (κ → ℝ)) (L : ι → StrongDual ℝ (κ → ℝ)) :
    (∫ x, L₀ x * ∏ i ∈ s, L i x ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) =
      ∑ i ∈ s, (∑ k, L₀ (Pi.single k 1) * L i (Pi.single k 1)) *
        ∫ x, ∏ j ∈ s.erase i, L j x ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
  have : IsGaussian (Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) := by
    apply (isGaussian_map_equiv_iff (EuclideanSpace.equiv κ ℝ).symm).mp
    -- The inverse coordinate equivalence is the canonical map into Euclidean space.
    convert (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ κ))) using 1
    exact map_pi_eq_stdGaussian
  have hlin (x : κ → ℝ) : L₀ x = ∑ k, L₀ (Pi.single k 1) * x k := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp only [map_sum]
    apply sum_congr rfl
    intro k _
    have hs : Pi.single k (x k) = x k • Pi.single k (1 : ℝ) := by
      simpa using Pi.single_smul (f := fun _ : κ ↦ ℝ) k (x k) (1 : ℝ)
    simp [hs, mul_comm]
  have hint (k : κ) : Integrable (fun x ↦ x k * ∏ i ∈ s, L i x)
      (Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) := by
    simpa [Finset.prod_image] using IsGaussian.integrable_prod_dual
      (Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) (insert none (s.image some))
      (fun i ↦ i.elim (ContinuousLinearMap.proj k) L) (fun _ ↦ 0)
  have hfun : (fun x ↦ L₀ x * ∏ i ∈ s, L i x) =
      fun x ↦ ∑ k, L₀ (Pi.single k 1) * (x k * ∏ i ∈ s, L i x) := by
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

/-- The centered multivariate Gaussian moment recursion. Pair the distinguished coordinate
with every remaining position and take the moment of the factors left over. Positions may
refer to repeated coordinates, and the covariance may be singular. -/
theorem integral_eval_mul_prod_multivariateGaussian {S : Matrix κ κ ℝ} (hS : S.PosSemidef)
    (s : Finset ι) (f : ι → κ) (k : κ) :
    (∫ x, x k * ∏ i ∈ s, x (f i) ∂multivariateGaussian 0 S) =
      ∑ i ∈ s, S k (f i) *
        ∫ x, ∏ j ∈ s.erase i, x (f j) ∂multivariateGaussian 0 S := by
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
  have hmap : (Measure.pi (fun _ : κ ↦ gaussianReal 0 1)).map T =
      multivariateGaussian 0 S := by
    rw [multivariateGaussian_zero_eq_map_stdGaussian_sqrt, ← map_pi_eq_stdGaussian,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hmom (t : Finset ι) :
      (∫ x, ∏ i ∈ t, L (f i) x ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1)) =
        ∫ x, ∏ i ∈ t, x (f i) ∂multivariateGaussian 0 S := by
    rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
    rfl
  have h := integral_dual_mul_prod_pi_gaussianReal s (L k) (fun i ↦ L (f i))
  simp only [hcoeff, hmom] at h
  calc
    _ = ∫ x, L k x * ∏ i ∈ s, L (f i) x
        ∂Measure.pi (fun _ : κ ↦ gaussianReal 0 1) := by
      rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := h

/-- The mixed-moment recursion centered at an arbitrary Gaussian mean. Each covariance
contracts two factors, leaving a centered moment of degree two less. -/
theorem integral_sub_mul_prod_sub_multivariateGaussian (m : EuclideanSpace ℝ κ)
    {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (s : Finset ι) (f : ι → κ) (k : κ) :
    (∫ x, (x k - m k) * ∏ i ∈ s, (x (f i) - m (f i)) ∂multivariateGaussian m S) =
      ∑ i ∈ s, S k (f i) *
        ∫ x, ∏ j ∈ s.erase i, (x (f j) - m (f j)) ∂multivariateGaussian m S := by
  have hshift : multivariateGaussian m S =
      (multivariateGaussian 0 S).map (fun x ↦ m + x) := by
    simp only [multivariateGaussian, zero_add]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hprod (t : Finset ι) :
      (∫ x, ∏ i ∈ t, (x (f i) - m (f i)) ∂multivariateGaussian m S) =
        ∫ x, ∏ i ∈ t, x (f i) ∂multivariateGaussian 0 S := by
    rw [hshift, integral_map (by fun_prop) (by fun_prop)]
    simp
  simp_rw [hprod]
  rw [hshift, integral_map (by fun_prop) (by fun_prop)]
  simpa using integral_eval_mul_prod_multivariateGaussian hS s f k

end Multivariate

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {ι κ Ω : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ κ}
  {m : EuclideanSpace ℝ κ} {S : Matrix κ κ ℝ}

/-- The centered mixed-moment recursion for a random vector with a multivariate Gaussian law.
Neither independence of coordinates nor nondegeneracy is required. -/
theorem integral_sub_mul_prod_sub_multivariateGaussian
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosSemidef)
    (s : Finset ι) (f : ι → κ) (k : κ) :
    (∫ ω, (X ω k - m k) * ∏ i ∈ s, (X ω (f i) - m (f i)) ∂P) =
      ∑ i ∈ s, S k (f i) *
        ∫ ω, ∏ j ∈ s.erase i, (X ω (f j) - m (f j)) ∂P := by
  have hprod (t : Finset ι) :
      (∫ ω, ∏ i ∈ t, (X ω (f i) - m (f i)) ∂P) =
        ∫ x, ∏ i ∈ t, (x (f i) - m (f i)) ∂multivariateGaussian m S :=
    hX.integral_comp (f := fun x : EuclideanSpace ℝ κ ↦
      ∏ i ∈ t, (x (f i) - m (f i))) (by fun_prop)
  simp_rw [hprod]
  calc
    _ = ∫ x, (x k - m k) * ∏ i ∈ s, (x (f i) - m (f i))
        ∂multivariateGaussian m S := hX.integral_comp (by fun_prop)
    _ = _ := TauCeti.Probability.integral_sub_mul_prod_sub_multivariateGaussian m hS s f k

end ProbabilityTheory.HasLaw
