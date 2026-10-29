/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import TauCeti.RingTheory.MvPolynomial.Jacobian

/-!
# Analytic derivatives of multivariate polynomial families

The formal partial derivatives of a multivariate polynomial give its Fréchet derivative on the
finite coordinate space over any nontrivially normed field. For a family of equations, with the
product topology on its target, this identifies the analytic derivative with the linear map of
`TauCeti.jacobiMatrixAt`.
-/

public section

open MvPolynomial

variable {𝕜 σ ι : Type*} [NontriviallyNormedField 𝕜] [Fintype σ]

/-- The derivative of polynomial evaluation is the sum of its evaluated formal partial
derivatives times the coordinate projections. -/
theorem MvPolynomial.hasFDerivAt_eval (p : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    HasFDerivAt (fun y ↦ eval y p)
      (∑ j, eval x (pderiv j p) • (ContinuousLinearMap.proj j : (σ → 𝕜) →L[𝕜] 𝕜)) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    convert! hasFDerivAt_const (𝕜 := 𝕜) a x using 1
    · simp
    · ext y
      simp
  | add p q hp hq =>
    convert! hp.add hq using 1
    · ext y
      simp
    · ext y
      simp [Finset.sum_add_distrib, add_mul]
  | mul_X p i hp =>
    convert! hp.mul (hasFDerivAt_apply i x) using 1
    · ext y
      simp
    · ext y
      simp [Finset.sum_add_distrib, mul_add, Finset.mul_sum,
        Pi.single_apply, apply_ite, mul_comm, mul_left_comm]

namespace TauCeti

/-- The analytic derivative of a polynomial family is its Jacobian matrix, viewed as a
continuous linear map. -/
theorem hasFDerivAt_eval_family (p : ι → MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    HasFDerivAt (fun y ↦ fun i ↦ eval y (p i))
      (ContinuousLinearMap.pi fun i ↦
        ∑ j, eval x (pderiv j (p i)) •
          (ContinuousLinearMap.proj j : (σ → 𝕜) →L[𝕜] 𝕜)) x :=
  hasFDerivAt_pi.mpr fun i ↦ (p i).hasFDerivAt_eval x

/-- The Fréchet derivative of a polynomial family agrees with its formal Jacobian. -/
theorem fderiv_eval_family (p : ι → MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    (fderiv 𝕜 (fun y ↦ fun i ↦ eval y (p i)) x).toLinearMap =
      (jacobiMatrixAt p x).mulVecLin := by
  classical
  rw [(hasFDerivAt_eval_family p x).fderiv]
  ext y i
  simp [Matrix.mulVec, dotProduct]

end TauCeti
