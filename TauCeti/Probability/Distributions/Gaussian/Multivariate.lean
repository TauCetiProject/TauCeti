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
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# The covariance matrix of a multivariate Gaussian

This file identifies the generic covariance matrix from
`TauCeti.Probability.Moments.Covariance` with the covariance parameter of Mathlib's multivariate
Gaussian, and records the centred multivariate Gaussian as the image of the standard Gaussian
under the square root of its matrix parameter. It also records measurability of Gaussian laws
with covariance scaled by a precision parameter, covariance under matrix-valued
linear maps and characterizes independence of complementary coordinate blocks.

## Main results

* `TauCeti.Probability.covMatrix_multivariateGaussian` recovers the covariance parameter of a
  multivariate
  Gaussian law.
* `TauCeti.Probability.integral_of_hasLaw_multivariateGaussian` gives the Bochner mean of a
  random variable with a multivariate Gaussian law.
* `TauCeti.Probability.multivariateGaussian_zero_eq_map_stdGaussian_sqrt` writes the centred law as
  an image
  of the standard Gaussian.
* `TauCeti.Probability.multivariateGaussian_zero_right` identifies the zero-covariance law with
  the point mass at its mean.
* `TauCeti.Probability.measurable_multivariateGaussian_inv_smul` shows that the family
  `τ ↦ N(m, τ⁻¹ • S)` is measurable in the precision `τ`.
* `TauCeti.Probability.measurable_multivariateGaussian_prodMk_left_apply` shows that the Gaussian
  law with measurable mean and covariance families, evaluated on a section of a measurable set, is
  measurable in the parameter.
* `TauCeti.Probability.covariance_inner_matrix_multivariateGaussian` computes covariance after two
  matrix
  maps.
* `TauCeti.Probability.indepFun_sumEquivProd_multivariateGaussian_iff` characterizes independence of
  two
  complementary coordinate blocks.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 1,
  **Covariance matrices**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace TauCeti.Probability

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

/-- Each coordinate of a multivariate Gaussian has as mean the corresponding coordinate of the
mean parameter. No hypothesis on the covariance parameter is needed. -/
@[simp]
theorem integral_eval_multivariateGaussian [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (i : ι) : ∫ x, x i ∂multivariateGaussian m S = m i := by
  simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian m S))

/-- The Bochner mean of a random variable with a multivariate Gaussian law is its Gaussian mean. -/
theorem integral_of_hasLaw_multivariateGaussian [Fintype ι] [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ ι}
    {S : Matrix ι ι ℝ} (hX : HasLaw X (multivariateGaussian m S) P) :
    ∫ ω, X ω ∂P = m := by
  rw [hX.integral_eq, integral_id_multivariateGaussian]

/-- A centred multivariate Gaussian law is the image of the standard Gaussian under the square
root of its matrix parameter. No hypothesis on that parameter is needed. -/
theorem multivariateGaussian_zero_eq_map_stdGaussian_sqrt [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) :
    multivariateGaussian 0 S =
      (stdGaussian (EuclideanSpace ℝ ι)).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) := by
  simp [multivariateGaussian]

/-- A multivariate Gaussian with zero covariance is the point mass at its mean. -/
@[simp]
theorem multivariateGaussian_zero_right [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m (0 : Matrix ι ι ℝ) = Measure.dirac m := by
  simp [multivariateGaussian]

/-- The Gaussian family `τ ↦ N(m, τ⁻¹ • S)` is measurable in the precision `τ`. -/
theorem measurable_multivariateGaussian_inv_smul [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measurable fun τ : ℝ => multivariateGaussian m (τ⁻¹ • S) :=
  measurable_multivariateGaussian.comp (measurable_const.prodMk (by fun_prop))

/-- For measurable mean and covariance families `m` and `S` on a measurable space `Y` and a
measurable map `g : Y → X`, the Gaussian law with mean `m y` and covariance `S y`, evaluated on
the section at `g y` of a measurable set `A ⊆ X × EuclideanSpace ℝ ι`, is measurable in `y`. -/
theorem measurable_multivariateGaussian_prodMk_left_apply [Fintype ι] [DecidableEq ι]
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {m : Y → EuclideanSpace ℝ ι}
    {S : Y → Matrix ι ι ℝ} {g : Y → X} (hm : Measurable m) (hS : Measurable S) (hg : Measurable g)
    {A : Set (X × EuclideanSpace ℝ ι)} (hA : MeasurableSet A) :
    Measurable fun y : Y => multivariateGaussian (m y) (S y) (Prod.mk (g y) ⁻¹' A) := by
  -- The law at `y` is Gaussian with mean `m y` and covariance `S y`; this is a kernel from `y`.
  let η : Kernel Y (EuclideanSpace ℝ ι) :=
    ⟨fun y => multivariateGaussian (m y) (S y),
      measurable_multivariateGaussian.comp (hm.prodMk hS)⟩
  have : IsMarkovKernel η := ⟨fun y => inferInstanceAs (IsProbabilityMeasure
    (multivariateGaussian (m y) (S y)))⟩
  -- The section of `{q | (g q.1, q.2) ∈ A}` at `y` is by definition the section of `A` at `g y`.
  exact Kernel.measurable_kernel_prodMk_left (κ := η)
    (t := {q : Y × EuclideanSpace ℝ ι | (g q.1, q.2) ∈ A})
    (hA.preimage ((hg.comp measurable_fst).prodMk measurable_snd))

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

/-- The pair of coordinate blocks of a multivariate Gaussian has a Gaussian law. -/
private lemma hasGaussianLaw_sumEquivProd_multivariateGaussian
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    HasGaussianLaw
      (fun x => ((EuclideanSpace.sumEquivProd x).1, (EuclideanSpace.sumEquivProd x).2))
      (multivariateGaussian m S) := by
  refine ⟨by fun_prop, ?_⟩
  -- Match the map field in the definition of `HasGaussianLaw`.
  change IsGaussian ((multivariateGaussian m S).map
    (EuclideanSpace.sumEquivProd : EuclideanSpace ℝ (ι ⊕ κ) →
      EuclideanSpace ℝ ι × EuclideanSpace ℝ κ))
  infer_instance

/-- Independent coordinate blocks of a multivariate Gaussian have vanishing cross-covariance
block. -/
private lemma submatrix_eq_zero_of_indepFun_sumEquivProd_multivariateGaussian
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hS : S.PosSemidef)
    (h : IndepFun (fun x => (EuclideanSpace.sumEquivProd x).1)
        (fun x => (EuclideanSpace.sumEquivProd x).2) (multivariateGaussian m S)) :
    S.submatrix Sum.inl Sum.inr = 0 := by
  have hpair := hasGaussianLaw_sumEquivProd_multivariateGaussian m S
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

/-- Vanishing cross-covariance block makes the coordinate blocks of a multivariate Gaussian
independent. -/
private lemma indepFun_sumEquivProd_multivariateGaussian_of_submatrix_eq_zero
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hS : S.PosSemidef)
    (hzero : S.submatrix Sum.inl Sum.inr = 0) :
    IndepFun (fun x => (EuclideanSpace.sumEquivProd x).1)
        (fun x => (EuclideanSpace.sumEquivProd x).2) (multivariateGaussian m S) := by
  have hpair := hasGaussianLaw_sumEquivProd_multivariateGaussian m S
  have hpair_eval : HasGaussianLaw
      (fun x => ((EuclideanSpace.sumEquivProd x).1.ofLp,
        (EuclideanSpace.sumEquivProd x).2.ofLp)) (multivariateGaussian m S) :=
    hpair.map_equiv_fun
      ((EuclideanSpace.equiv ι ℝ).prodCongr (EuclideanSpace.equiv κ ℝ))
  have hind_eval := hpair_eval.indepFun_of_covariance_eval fun i j => by
    have hentry := covariance_eval_multivariateGaussian (μ := m) hS (Sum.inl i) (Sum.inr j)
    -- The coordinate functions from `map_equiv_fun` reduce through `sumEquivProd` and
    -- `EuclideanSpace.equiv` only definitionally; there is no named rewrite lemma exposing them.
    change cov[fun x => x.ofLp (Sum.inl i), fun x => x.ofLp (Sum.inr j);
      multivariateGaussian m S] = 0
    rw [hentry]
    exact congrFun (congrFun hzero i) j
  convert hind_eval.comp (by fun_prop : Measurable (EuclideanSpace.equiv ι ℝ).symm)
    (by fun_prop : Measurable (EuclideanSpace.equiv κ ℝ).symm) using 1 <;> ext x i <;> rfl

/-- The two complementary coordinate blocks of a multivariate Gaussian with positive-semidefinite
covariance are independent exactly when their cross-covariance block vanishes. -/
theorem indepFun_sumEquivProd_multivariateGaussian_iff
    {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hS : S.PosSemidef) :
    IndepFun (fun x => (EuclideanSpace.sumEquivProd x).1)
        (fun x => (EuclideanSpace.sumEquivProd x).2) (multivariateGaussian m S) ↔
      S.submatrix Sum.inl Sum.inr = 0 :=
  ⟨submatrix_eq_zero_of_indepFun_sumEquivProd_multivariateGaussian m hS,
    indepFun_sumEquivProd_multivariateGaussian_of_submatrix_eq_zero m hS⟩

end TauCeti.Probability
