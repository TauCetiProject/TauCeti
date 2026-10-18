/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Independence of linear images of a multivariate Gaussian

This file characterizes independence of two rectangular linear images of a multivariate Gaussian
vector.  The images are independent exactly when their cross-covariance matrix vanishes.  The
result applies to singular covariance matrices and to maps with arbitrary finite-dimensional
codomains.

## Main results

* `TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff` characterizes independence under
  the Gaussian measure itself.
* `TauCeti.Probability.indepFun_matrix_of_hasLaw_multivariateGaussian_iff` gives the corresponding
  statement for a random vector with that law.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

namespace TauCeti.Probability

variable {ι κ τ : Type*} [Fintype ι] [Finite κ] [Finite τ]
  [DecidableEq ι]

/-- Two rectangular linear images of a multivariate Gaussian are independent exactly when their
cross-covariance matrix vanishes. -/
theorem indepFun_matrix_multivariateGaussian_iff
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (A : Matrix κ ι ℝ) (B : Matrix τ ι ℝ) :
    IndepFun (fun x => A.toEuclideanLin x) (fun x => B.toEuclideanLin x)
        (multivariateGaussian m S) ↔
      A * S * B.transpose = 0 := by
  classical
  let _ := Fintype.ofFinite κ
  let _ := Fintype.ofFinite τ
  have hA : HasGaussianLaw (fun x : EuclideanSpace ℝ ι => A.toEuclideanLin x)
      (multivariateGaussian m S) :=
    IsGaussian.hasGaussianLaw_id.map_fun A.toEuclideanLin.toContinuousLinearMap
  have hB : HasGaussianLaw (fun x : EuclideanSpace ℝ ι => B.toEuclideanLin x)
      (multivariateGaussian m S) :=
    IsGaussian.hasGaussianLaw_id.map_fun B.toEuclideanLin.toContinuousLinearMap
  constructor
  · intro hindep
    ext i j
    have hcov :
        cov[fun x => ⟪EuclideanSpace.single i 1, A.toEuclideanLin x⟫,
          fun x => ⟪EuclideanSpace.single j 1, B.toEuclideanLin x⟫;
          multivariateGaussian m S] = 0 := by
      exact (hindep.comp (by fun_prop) (by fun_prop)).covariance_eq_zero
        (hA.map_fun (innerSL ℝ (EuclideanSpace.single i 1))).memLp_two
        (hB.map_fun (innerSL ℝ (EuclideanSpace.single j 1))).memLp_two
    rw [covariance_inner_matrix_multivariateGaussian m hS] at hcov
    simpa using hcov
  · intro hcross
    let L : EuclideanSpace ℝ ι →L[ℝ]
        EuclideanSpace ℝ κ × EuclideanSpace ℝ τ :=
      A.toEuclideanLin.toContinuousLinearMap.prod B.toEuclideanLin.toContinuousLinearMap
    have hpair :=
      IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian m S) |>.map_fun L
    refine hpair.indepFun_of_covariance_inner fun x y => ?_
    -- Unfold the two projections of the product map `L` to expose the `A`- and `B`-images
    -- expected by `covariance_inner_matrix_multivariateGaussian`.
    change cov[fun z => ⟪x, A.toEuclideanLin z⟫, fun z => ⟪y, B.toEuclideanLin z⟫;
      multivariateGaussian m S] = 0
    rw [covariance_inner_matrix_multivariateGaussian m hS, hcross]
    simp

/-- Linear images of a random vector with a multivariate Gaussian law are independent exactly when
their cross-covariance matrix vanishes. -/
theorem indepFun_matrix_of_hasLaw_multivariateGaussian_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}
    {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hX : HasLaw X (multivariateGaussian m S) P) (A : Matrix κ ι ℝ) (B : Matrix τ ι ℝ) :
    IndepFun (fun ω => A.toEuclideanLin (X ω)) (fun ω => B.toEuclideanLin (X ω)) P ↔
      A * S * B.transpose = 0 := by
  classical
  let _ := Fintype.ofFinite κ
  let _ := Fintype.ofFinite τ
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hpair : IdentDistrib
      (fun ω => (A.toEuclideanLin (X ω), B.toEuclideanLin (X ω)))
      (fun x : EuclideanSpace ℝ ι => (A.toEuclideanLin x, B.toEuclideanLin x)) P
      (multivariateGaussian m S) := by
    let f : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ × EuclideanSpace ℝ τ :=
      fun x => (A.toEuclideanLin x, B.toEuclideanLin x)
    exact (HasLaw.fun_comp (hasLaw_map (P := multivariateGaussian m S)
      (X := f) (by fun_prop)) hX).identDistrib
        (hasLaw_map (P := multivariateGaussian m S) (X := f) (by fun_prop))
  constructor
  · intro hindep
    exact (indepFun_matrix_multivariateGaussian_iff m hS A B).1
      (indepFun_of_identDistrib_pair hindep hpair)
  · intro hcross
    exact indepFun_of_identDistrib_pair
      ((indepFun_matrix_multivariateGaussian_iff m hS A B).2 hcross) hpair.symm

end TauCeti.Probability
