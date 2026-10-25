/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivatives of polynomial functions along a coordinate line

For a polynomial `F` in variables indexed by `ι` over a nontrivially normed field and a point
`x`, the function `w ↦ F(x₁, …, w, …)` obtained by varying the coordinate `xᵢ` has derivative
`w ↦ (∂F/∂Xᵢ)(x₁, …, w, …)`. Iterating, the derivatives along this line of the exponential
polynomial `w ↦ F(…, w, …) exp(a w + b)` are given by the Leibniz rule

`(d/dw)^σ [F(…, w, …) exp(a w + b)] = (∑_{k ≤ σ} (σ choose k) a^(σ - k) (∂ᵏF/∂Xᵢᵏ)(…, w, …))
  exp(a w + b)`.

This is the form in which derivatives of the auxiliary functions `z^τ exp(t ⟨λ, z⟩)` of
transcendence theory are evaluated in interpolation determinants.

## Main results

* `MvPolynomial.hasDerivAt_eval_update`: the derivative along the `i`-th coordinate line is the
  evaluated partial derivative `pderiv i`.
* `MvPolynomial.iteratedDeriv_eval_update_mul_cexp`: the Leibniz formula above.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.1.
-/

public section

open Finset Function

namespace MvPolynomial

section Field

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι]

/-- The derivative of a polynomial function along the `i`-th coordinate line through `x` is the
partial derivative `pderiv i`, evaluated on the same line. -/
theorem hasDerivAt_eval_update (F : MvPolynomial ι 𝕜) (x : ι → 𝕜) (i : ι) (w : 𝕜) :
    HasDerivAt (fun w ↦ eval (update x i w) F) (eval (update x i w) (pderiv i F)) w := by
  induction F using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const w a
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p j hp =>
    obtain rfl | hj := eq_or_ne j i
    · simpa only [eval_mul, eval_X, pderiv_mul, pderiv_X_self, update_self, map_add, mul_one]
        using hp.fun_mul (hasDerivAt_id' w)
    · simp only [eval_mul, eval_X, pderiv_mul, pderiv_X_of_ne hj, update_of_ne hj,
        mul_zero, add_zero]
      exact hp.mul_const (x j)

end Field

/-- The Leibniz formula for the iterated derivatives along the `i`-th coordinate line of the
exponential polynomial `w ↦ F(…, w, …) exp(a w + b)`:
`(d/dw)^σ = ∑_{k ≤ σ} (σ choose k) a^(σ - k) (∂ᵏF/∂Xᵢᵏ)(…, w, …) exp(a w + b)`. -/
theorem iteratedDeriv_eval_update_mul_cexp {ι : Type*} [DecidableEq ι] (F : MvPolynomial ι ℂ)
    (x : ι → ℂ) (i : ι) (a b : ℂ) (σ : ℕ) :
    iteratedDeriv σ (fun w ↦ eval (update x i w) F * Complex.exp (a * w + b)) = fun w ↦
      (∑ k ∈ range (σ + 1), (σ.choose k : ℂ) * a ^ (σ - k) *
        eval (update x i w) ((pderiv i)^[k] F)) * Complex.exp (a * w + b) := by
  -- The derivative of `F(…, w, …) exp(a w + b)` is `G(…, w, …) exp(a w + b)` with
  -- `G = (∂/∂Xᵢ + a) F`, so the `σ`-th derivative is given by the operator `(∂/∂Xᵢ + a) ^ σ`.
  set D : Module.End ℂ (MvPolynomial ι ℂ) := (pderiv i).toLinearMap
  have hderiv (G : MvPolynomial ι ℂ) :
      deriv (fun w ↦ eval (update x i w) G * Complex.exp (a * w + b)) = fun w ↦
        eval (update x i w) ((D + a • 1) G) * Complex.exp (a * w + b) := by
    funext w
    have hexp : HasDerivAt (fun w ↦ Complex.exp (a * w + b)) (Complex.exp (a * w + b) * a) w :=
      (((hasDerivAt_id w).const_mul a).add_const b).cexp.congr_deriv (by simp)
    rw [((hasDerivAt_eval_update G x i w).fun_mul hexp).deriv]
    simp [D, smul_eval]
    ring
  have hop : iteratedDeriv σ (fun w ↦ eval (update x i w) F * Complex.exp (a * w + b)) =
      fun w ↦ eval (update x i w) (((D + a • 1) ^ σ) F) * Complex.exp (a * w + b) := by
    induction σ with
    | zero => simp
    | succ σ ih => rw [iteratedDeriv_succ, ih, hderiv, pow_succ', Module.End.mul_apply]
  rw [hop, ((Commute.one_right D).smul_right a).add_pow]
  funext w
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.natCast_apply, smul_pow,
    one_pow, LinearMap.smul_apply, Module.End.one_apply, map_nsmul, map_smul, map_sum,
    Finset.sum_mul]
  simp only [Module.End.pow_apply, D, Derivation.coeFn_coe, smul_eval, nsmul_eq_mul, mul_assoc]

end MvPolynomial
