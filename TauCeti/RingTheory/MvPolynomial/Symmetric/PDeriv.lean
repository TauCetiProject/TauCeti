/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous

/-!
# Partial derivatives of the elementary symmetric polynomials

For a family `μ : σ → R` and a variable `i`, write `σ_k(μ)` for the value of the elementary
symmetric polynomial `e_k` at `μ`, and `σ_{k;i}(μ) = σ_k(μ)|_{μ_i = 0}` for its value with the
`i`-th entry set to zero, which is `e_k` of the remaining entries. Since `e_{k+1}` is affine in
each variable,

`σ_{k+1}(μ) = μ_i σ_{k;i}(μ) + σ_{k+1;i}(μ)`

(`TauCeti.aeval_esymm_succ_eq_mul_add`), and the partial derivative of `e_{k+1}` in `X_i` is
`e_k` with `X_i` set to zero, that is `∂σ_{k+1}/∂μ_i = σ_{k;i}`. Summing the partial
derivatives against the variables gives Euler's identity
`∑_i μ_i σ_{k;i}(μ) = (k + 1) σ_{k+1}(μ)`, and summing them alone gives
`∑_i σ_{k;i}(μ) = (n - k) σ_k(μ)` for `n` variables (`TauCeti.sum_eval_update_zero_esymm`).
The recurrence and this last sum are purely algebraic and live with the other identities of the
elementary symmetric functions in `TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary`.

These are the identities through which the elementary symmetric functions enter the theory of
the Gårding cones `Γ_k = {σ_1 > 0, …, σ_k > 0}` and of the complex Hessian equations, whose
linearisation involves the partial derivatives `σ_{k-1;i}` of `σ_k`.

## Main results

* `TauCeti.pderiv_esymm_succ` and `TauCeti.eval_pderiv_esymm_succ`: `∂e_{k+1}/∂X_i` is `e_k`
  with `X_i` set to zero, and its value at `μ` is `σ_{k;i}(μ)`.
* `TauCeti.sum_pderiv_esymm_succ`: `∑_i ∂e_{k+1}/∂X_i = (n - k) e_k` in `n` variables.
* `TauCeti.sum_mul_eval_update_zero_esymm`: Euler's identity
  `∑_i μ_i σ_{k;i}(μ) = (k + 1) σ_{k+1}(μ)`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, in *Global
  theory of minimal surfaces*, Clay Math. Proc. **2** (2005), 283–309, §2.
* S. Dinew and S. Kołodziej, *A priori estimates for complex Hessian equations*, Anal. PDE **7**
  (2014), 227–244, §1.
-/

public section

open Finset Function MvPolynomial

namespace TauCeti

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

/-- **The partial derivatives of the elementary symmetric polynomials**: `∂e_{k+1}/∂X_i` is `e_k`
with the variable `X_i` set to zero, that is, `e_k` of the variables other than `X_i`. -/
theorem pderiv_esymm_succ (i : σ) (k : ℕ) :
    pderiv i (esymm σ R (k + 1)) = aeval (update X i 0 : σ → MvPolynomial σ R) (esymm σ R k) := by
  have h0 : ∀ m, pderiv i (aeval (update X i 0 : σ → MvPolynomial σ R) (esymm σ R m)) = 0 := by
    intro m
    rw [pderiv_aeval]
    refine sum_eq_zero fun j _ ↦ ?_
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [update_of_ne hj, pderiv_X_of_ne hj]
  conv_lhs => rw [← aeval_X_left_apply (esymm σ R (k + 1)), aeval_esymm_succ_eq_mul_add X i k]
  simp [h0]

/-- **The partial derivatives of the elementary symmetric functions**, evaluated:
`∂σ_{k+1}/∂μ_i (μ) = σ_{k;i}(μ)`, the value of `e_k` with the `i`-th entry of `μ` set to zero. -/
@[simp]
theorem eval_pderiv_esymm_succ (μ : σ → R) (i : σ) (k : ℕ) :
    eval μ (pderiv i (esymm σ R (k + 1))) = eval (update μ i 0) (esymm σ R k) := by
  have h : (fun j ↦ aeval μ (update X i 0 j : MvPolynomial σ R)) = update μ i 0 := by
    funext j
    rcases eq_or_ne j i with rfl | hj <;> simp [*]
  rw [pderiv_esymm_succ, ← aeval_eq_eval, comp_aeval_apply, h, aeval_eq_eval]

omit [DecidableEq σ] in
/-- **The derivative of `e_{k+1}` in the direction `(1, …, 1)`**: in `n` variables,
`∑_i ∂e_{k+1}/∂X_i = (n - k) e_k`. -/
theorem sum_pderiv_esymm_succ (k : ℕ) :
    ∑ i, pderiv i (esymm σ R (k + 1)) = ((Fintype.card σ - k : ℕ) : R) • esymm σ R k := by
  classical
  -- Evaluate `∑_i σ_{k;i}(μ) = (n - k) σ_k(μ)` at the variables, in the ring of polynomials.
  have h := sum_eval_update_zero_esymm (X : σ → MvPolynomial σ R) k
  simp_rw [pderiv_esymm_succ]
  simp only [esymm, map_sum, map_prod, eval_X, aeval_X] at h ⊢
  rw [h, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/-- **Euler's identity for the elementary symmetric functions**:
`∑_i μ_i σ_{k;i}(μ) = (k + 1) σ_{k+1}(μ)`, where `σ_{k;i}(μ)` is the value of `e_k` with the
`i`-th entry of `μ` set to zero. -/
theorem sum_mul_eval_update_zero_esymm (μ : σ → R) (k : ℕ) :
    ∑ i, μ i * eval (update μ i 0) (esymm σ R k) = (k + 1) * eval μ (esymm σ R (k + 1)) := by
  have h := congrArg (MvPolynomial.eval μ)
    (isHomogeneous_esymm (σ := σ) (R := R) (k + 1)).sum_X_mul_pderiv
  simpa [nsmul_eq_mul] using h

end TauCeti
