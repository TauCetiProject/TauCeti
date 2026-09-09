/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Moments.Covariance

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# The covariance matrix of a multivariate Gaussian

This file identifies the generic covariance matrix from
`TauCeti.Probability.Moments.Covariance` with the covariance parameter of Mathlib's multivariate
Gaussian, and records the centred multivariate Gaussian as the image of the standard Gaussian
under the square root of its matrix parameter. It also records covariance under matrix-valued
linear maps and characterizes independence of complementary coordinate blocks.

## Main results

* `TauCeti.covMatrix_multivariateGaussian` recovers the covariance parameter of a multivariate
  Gaussian law.
* `TauCeti.multivariateGaussian_zero_eq_map_stdGaussian_sqrt` writes the centred law as an image
  of the standard Gaussian.
* `TauCeti.covariance_inner_matrix_multivariateGaussian` computes covariance after two matrix
  maps.
* `TauCeti.indepFun_sumEquivProd_multivariateGaussian_iff` characterizes independence of two
  complementary coordinate blocks.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 1,
  **Covariance matrices**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace TauCeti

variable {ι : Type*}

/-- The covariance matrix of a positive-semidefinite multivariate Gaussian is its covariance
parameter. -/
@[simp]
theorem covMatrix_multivariateGaussian [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    covMatrix (multivariateGaussian m S) = S := by
  classical
  ext i j
  simpa only [covMatrix_apply] using covariance_eval_multivariateGaussian hS i j

/-- A centred multivariate Gaussian law is the image of the standard Gaussian under the square
root of its matrix parameter. No hypothesis on that parameter is needed. -/
theorem multivariateGaussian_zero_eq_map_stdGaussian_sqrt [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) :
    multivariateGaussian 0 S =
      (stdGaussian (EuclideanSpace ℝ ι)).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) := by
  simp [multivariateGaussian]

/-- The covariance of scalar inner-product projections after two matrix-valued linear maps of a
multivariate Gaussian. -/
theorem covariance_inner_matrix_multivariateGaussian
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ]
    (m : EuclideanSpace ℝ γ) {S : Matrix γ γ ℝ} (hS : S.PosSemidef)
    (L : Matrix α γ ℝ) (K : Matrix β γ ℝ) (x : EuclideanSpace ℝ α)
    (y : EuclideanSpace ℝ β) :
    cov[fun z => ⟪x, L.toEuclideanLin z⟫, fun z => ⟪y, K.toEuclideanLin z⟫;
      multivariateGaussian m S] =
      x.ofLp ⬝ᵥ (L * S * K.transpose).mulVec y.ofLp := by
  classical
  have hL : (fun z => ⟪x, L.toEuclideanLin z⟫) =
      fun z => ⟪L.transpose.toEuclideanLin x, z⟫ := by
    funext z
    symm
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial L,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hK : (fun z => ⟪y, K.toEuclideanLin z⟫) =
      fun z => ⟪K.transpose.toEuclideanLin y, z⟫ := by
    funext z
    symm
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial K,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  rw [hL, hK, ← covarianceBilin_apply_eq_cov,
    covarianceBilin_multivariateGaussian hS]
  · have hLapply : (L.transpose.toEuclideanLin x).ofLp = L.transpose.mulVec x.ofLp := by
      simpa only [Matrix.toLin'_apply] using
        Matrix.ofLp_toLpLin (p := 2) (q := 2) L.transpose x
    have hKapply : (K.transpose.toEuclideanLin y).ofLp = K.transpose.mulVec y.ofLp := by
      simpa only [Matrix.toLin'_apply] using
        Matrix.ofLp_toLpLin (p := 2) (q := 2) K.transpose y
    rw [hLapply, hKapply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    calc
      L.transpose.mulVec x.ofLp ⬝ᵥ S.mulVec (K.transpose.mulVec y.ofLp) =
          Matrix.vecMul x.ofLp L ⬝ᵥ S.mulVec (K.transpose.mulVec y.ofLp) := by
        rw [Matrix.mulVec_transpose]
      _ = x.ofLp ⬝ᵥ L.mulVec (S.mulVec (K.transpose.mulVec y.ofLp)) :=
        (Matrix.dotProduct_mulVec x.ofLp L
          (S.mulVec (K.transpose.mulVec y.ofLp))).symm
  · exact IsGaussian.memLp_two_id

/-- The two complementary coordinate blocks of a multivariate Gaussian with positive-semidefinite
covariance are independent exactly when their cross-covariance block vanishes. -/
theorem indepFun_sumEquivProd_multivariateGaussian_iff
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hS : S.PosSemidef) :
    IndepFun (fun x => (EuclideanSpace.sumEquivProd x).1)
        (fun x => (EuclideanSpace.sumEquivProd x).2) (multivariateGaussian m S) ↔
      S.submatrix Sum.inl Sum.inr = 0 := by
  have hpair : HasGaussianLaw
      (fun x => ((EuclideanSpace.sumEquivProd x).1, (EuclideanSpace.sumEquivProd x).2))
      (multivariateGaussian m S) := by
    refine ⟨by fun_prop, ?_⟩
    -- Match the map field in the definition of `HasGaussianLaw`.
    change IsGaussian ((multivariateGaussian m S).map
      (EuclideanSpace.sumEquivProd : EuclideanSpace ℝ (ι ⊕ κ) →
        EuclideanSpace ℝ ι × EuclideanSpace ℝ κ))
    infer_instance
  constructor
  · intro h
    ext i j
    have hmeasurable_i : Measurable (fun x : EuclideanSpace ℝ ι => x.ofLp i) := by fun_prop
    have hmeasurable_j : Measurable (fun x : EuclideanSpace ℝ κ => x.ofLp j) := by fun_prop
    have hind := h.comp hmeasurable_i hmeasurable_j
    have hi := hpair.fst.map_fun (EuclideanSpace.proj i)
    have hj := hpair.snd.map_fun (EuclideanSpace.proj j)
    have hmemi : MemLp
        ((fun x : EuclideanSpace ℝ ι => x.ofLp i) ∘
          fun x => (EuclideanSpace.sumEquivProd x).1) 2
        (multivariateGaussian m S) := by
      convert hi.memLp_two using 1
      funext x
      rfl
    have hmemj : MemLp
        ((fun x : EuclideanSpace ℝ κ => x.ofLp j) ∘
          fun x => (EuclideanSpace.sumEquivProd x).2) 2
        (multivariateGaussian m S) := by
      convert hj.memLp_two using 1
      funext x
      rfl
    have hcov := hind.covariance_eq_zero hmemi hmemj
    have hentry := covariance_eval_multivariateGaussian (μ := m) hS (Sum.inl i) (Sum.inr j)
    -- Unfold the submatrix entry selected by extensionality.
    change S (Sum.inl i) (Sum.inr j) = 0
    rw [← hentry]
    have hfst : (fun x : EuclideanSpace ℝ (ι ⊕ κ) => x.ofLp (Sum.inl i)) =
        (fun x : EuclideanSpace ℝ ι => x.ofLp i) ∘
          fun x => (EuclideanSpace.sumEquivProd x).1 := by
      funext x
      rfl
    have hsnd : (fun x : EuclideanSpace ℝ (ι ⊕ κ) => x.ofLp (Sum.inr j)) =
        (fun x : EuclideanSpace ℝ κ => x.ofLp j) ∘
          fun x => (EuclideanSpace.sumEquivProd x).2 := by
      funext x
      rfl
    rw [hfst, hsnd]
    exact hcov
  · intro hzero
    have hpair_eval : HasGaussianLaw
        (fun x => ((EuclideanSpace.sumEquivProd x).1.ofLp,
          (EuclideanSpace.sumEquivProd x).2.ofLp)) (multivariateGaussian m S) :=
      hpair.map_equiv_fun
        ((EuclideanSpace.equiv ι ℝ).prodCongr (EuclideanSpace.equiv κ ℝ))
    have hind_eval := hpair_eval.indepFun_of_covariance_eval fun i j => by
      have hentry := covariance_eval_multivariateGaussian (μ := m) hS (Sum.inl i) (Sum.inr j)
      change cov[fun x => x.ofLp (Sum.inl i), fun x => x.ofLp (Sum.inr j);
        multivariateGaussian m S] = 0
      rw [hentry]
      exact congrFun (congrFun hzero i) j
    convert hind_eval.comp (by fun_prop : Measurable (EuclideanSpace.equiv ι ℝ).symm)
      (by fun_prop : Measurable (EuclideanSpace.equiv κ ℝ).symm) using 1 <;> ext x i <;> rfl

end TauCeti
