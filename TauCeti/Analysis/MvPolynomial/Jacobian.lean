/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import TauCeti.RingTheory.MvPolynomial.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Analytic derivatives of multivariate polynomial families

The formal partial derivatives of a multivariate polynomial give its Fréchet derivative on the
finite coordinate space over any nontrivially normed field. For a family of equations, with the
product topology on its target, this identifies the analytic derivative with the linear map of
`TauCeti.jacobiMatrixAt`. In particular the derivative is surjective exactly when the Jacobian
matrix is, and over a complete field the evaluation map of the family is analytic.

For a polynomial relation `P (y, f y) = 0` between the coordinates and the values of a
differentiable function `f`, with `P : (MvPolynomial σ 𝕜)[X]`, differentiating in a direction `v`
gives the implicit differentiation identity `P_t (y, f y) * Df(y) v + (D_v P) (y, f y) = 0`
(`TauCeti.eventually_eval_derivative_mul_fderiv_add_eval_derivCoeffs`). Here `P_t` is the
derivative of `P` in the value variable and `D_v P` (`TauCeti.derivCoeffs`) differentiates the
coefficients of `P` in the direction `v`.
-/

public section

open MvPolynomial Topology
open scoped Polynomial

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

/-- The Fréchet derivative of a polynomial family is surjective exactly when its Jacobian matrix
is. -/
theorem surjective_fderiv_eval_family_iff (p : ι → MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    Function.Surjective (fderiv 𝕜 (fun y ↦ fun i ↦ eval y (p i)) x) ↔
      Function.Surjective (jacobiMatrixAt p x).mulVec := by
  have h := congrArg (fun T : (σ → 𝕜) →ₗ[𝕜] (ι → 𝕜) ↦ ⇑T) (fderiv_eval_family p x)
  simp only [ContinuousLinearMap.coe_coe, Matrix.coe_mulVecLin] at h
  rw [h]

/-- Over a complete field, the evaluation map of a polynomial family is analytic. -/
theorem analyticOnNhd_eval_family [CompleteSpace 𝕜] [Fintype ι] (p : ι → MvPolynomial σ 𝕜) :
    AnalyticOnNhd 𝕜 (fun x : σ → 𝕜 ↦ fun i ↦ eval x (p i)) Set.univ :=
  AnalyticOnNhd.pi fun i ↦ AnalyticOnNhd.eval_mvPolynomial (p i)

section ImplicitDifferentiation

variable {f : (σ → 𝕜) → 𝕜}

/-- The derivative of `y ↦ ∑ k < N, c_k(y) * f(y) ^ k` in the direction `v`, for polynomial
coefficients `c_k`, is `(∑ k < N, k * c_k(y) * f(y) ^ (k - 1)) * Df(y) v` plus
`∑ k < N, (D_v c_k)(y) * f(y) ^ k`. -/
theorem fderiv_sum_eval_mul_pow_apply (c : ℕ → MvPolynomial σ 𝕜) (N : ℕ) {y : σ → 𝕜}
    (hfy : DifferentiableAt 𝕜 f y) (v : σ → 𝕜) :
    fderiv 𝕜 (fun z ↦ ∑ k ∈ Finset.range N, eval z (c k) * f z ^ k) y v =
      (∑ k ∈ Finset.range N, eval y (c k) * k * f y ^ (k - 1)) * fderiv 𝕜 f y v +
        ∑ k ∈ Finset.range N, eval y (∑ j, C (v j) * pderiv j (c k)) * f y ^ k := by
  have hd := HasFDerivAt.fun_sum (u := Finset.range N) fun k _ ↦
    ((c k).hasFDerivAt_eval y).fun_mul (hfy.hasFDerivAt.pow k)
  rw [hd.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, map_sum, map_mul, eval_C,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The polynomial obtained from `P` by differentiating its coefficients in the direction `v`. -/
noncomputable def derivCoeffs (v : σ → 𝕜) (P : (MvPolynomial σ 𝕜)[X]) : (MvPolynomial σ 𝕜)[X] :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    Polynomial.monomial k (∑ j, C (v j) * pderiv j (P.coeff k))

/-- **Implicit differentiation.** If `f` is differentiable near `x` and `P (y, f y) = 0` near `x`,
then near `x`, `P_t (y, f y) * Df(y) v + (D_v P) (y, f y) = 0`, where `P_t` is the derivative of
`P` in the value variable and `D_v P` is `TauCeti.derivCoeffs v P`. -/
theorem eventually_eval_derivative_mul_fderiv_add_eval_derivCoeffs {x : σ → 𝕜}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y) {P : (MvPolynomial σ 𝕜)[X]}
    (hP : ∀ᶠ y in 𝓝 x, (P.map (eval y)).eval (f y) = 0) (v : σ → 𝕜) :
    ∀ᶠ y in 𝓝 x, ((Polynomial.derivative P).map (eval y)).eval (f y) * fderiv 𝕜 f y v +
      ((derivCoeffs v P).map (eval y)).eval (f y) = 0 := by
  set N := P.natDegree + 1
  have hPsum : P = ∑ k ∈ Finset.range N, Polynomial.monomial k (P.coeff k) :=
    Polynomial.as_sum_range' P N (Nat.lt_succ_self _)
  have hrel : ∀ᶠ y in 𝓝 x, ∑ k ∈ Finset.range N, eval y (P.coeff k) * f y ^ k = 0 := by
    filter_upwards [hP] with y hy
    rw [hPsum] at hy
    simpa [Polynomial.map_sum, Polynomial.eval_finsetSum] using hy
  filter_upwards [hrel.eventually_nhds, hf] with y hy hfy
  have h0 := fderiv_sum_eval_mul_pow_apply (fun k ↦ P.coeff k) N hfy v
  rw [Filter.EventuallyEq.fderiv_eq (f := 0) hy, fderiv_zero, Pi.zero_apply, zero_apply] at h0
  nth_rewrite 1 [hPsum]
  simp only [derivCoeffs, Polynomial.derivative_sum, Polynomial.derivative_monomial,
    Polynomial.map_sum, Polynomial.map_monomial, map_mul, map_natCast]
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  rw [h0]

end ImplicitDifferentiation

end TauCeti
