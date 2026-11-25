/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Laguerre.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.RingTheory.Polynomial.Laguerre.Recurrence
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Rodrigues formula for the Laguerre polynomials

The generalized Laguerre polynomials `Lₙ^{(α)} = Polynomial.laguerre α n` with a real parameter
`α` are given on the half-line `(0, ∞)` by the Rodrigues formula (DLMF 18.5.5 with Table 18.5.1)

`Lₙ^{(α)}(x) = x ^ (-α) * exp x / n! * dⁿ/dxⁿ (exp (-x) * x ^ (n + α))`.

For real `α` the function `x ^ (n + α)` is not a polynomial, so this is a statement about real
functions, with `Real.rpow` powers and the hypothesis `0 < x`, and not an identity of polynomials.

The formula is the case `β = n + α`, `j = n` of a formula for every derivative of
`exp (-t) * t ^ β`: for every real `β` and `0 < t`,

`dʲ/dtʲ (exp (-t) * t ^ β) = j! * (exp (-t) * t ^ (β - j)) * L_j^{(β - j)}(t)`.

It is proved by induction on `j`; the inductive step is the raising relation
`Polynomial.X_mul_derivative_laguerre_add_one`. The derivatives of order `j < n` of
`exp (-t) * t ^ (n + α)` are the boundary terms of the integration by parts that proves the
Laguerre orthogonality relation, so the general formula is stated for every `j`.

## Main statements

* `Polynomial.hasDerivAt_exp_neg_mul_rpow_mul_laguerre`: for `0 < t`, the derivative at `t` of
  `exp (-s) * s ^ (γ + 1) * L_j^{(γ + 1)}(s)` is `(j + 1) * (exp (-t) * t ^ γ) * L_{j+1}^{(γ)}(t)`.
* `Polynomial.iteratedDeriv_exp_neg_mul_rpow_eq_laguerre`: for `0 < t`, every real `β` and every
  `j`, the `j`-th derivative of `exp (-t) * t ^ β` at `t`.
* `Polynomial.laguerre_rodrigues`: the Rodrigues formula, for `0 < x` and every real `α`.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, 18.5.5 with
  Table 18.5.1.
* G. Szegő, *Orthogonal Polynomials*, Ch. V, (5.1.5).
-/

public section

namespace Polynomial

open Real

/-- One step of the Rodrigues formula: on `(0, ∞)`, differentiating
`exp (-t) * t ^ (γ + 1) * L_j^{(γ + 1)}(t)` lowers the parameter and raises the index. -/
theorem hasDerivAt_exp_neg_mul_rpow_mul_laguerre (γ : ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => exp (-s) * s ^ (γ + 1) * (laguerre (γ + 1) j).eval s)
      ((j + 1) * (exp (-t) * t ^ γ) * (laguerre γ (j + 1)).eval t) t := by
  have h₁ : HasDerivAt (fun s : ℝ => exp (-s)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have h₂ : HasDerivAt (fun s : ℝ => s ^ (γ + 1)) ((γ + 1) * t ^ γ) t := by
    simpa using hasDerivAt_rpow_const (p := γ + 1) (Or.inl ht.ne')
  have h := congrArg (eval t) (X_mul_derivative_laguerre_add_one γ j)
  simp only [eval_mul, eval_X, eval_sub, eval_C, eval_add, eval_one, eval_natCast, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at h
  refine ((h₁.fun_mul h₂).fun_mul ((laguerre (γ + 1) j).hasDerivAt t)).congr_deriv ?_
  rw [rpow_add_one ht.ne']
  linear_combination (exp (-t) * t ^ γ) * h

/-- The derivatives of `exp (-t) * t ^ β` on `(0, ∞)`: for real `β`,
`dʲ/dtʲ (exp (-t) * t ^ β) = j! * (exp (-t) * t ^ (β - j)) * L_j^{(β - j)}(t)`.
At `β = n + α`, `j = n` this is the Rodrigues formula `Polynomial.laguerre_rodrigues`. -/
theorem iteratedDeriv_exp_neg_mul_rpow_eq_laguerre (β : ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv j (fun s : ℝ => exp (-s) * s ^ β) t =
      j.factorial * (exp (-t) * t ^ (β - j)) * (laguerre (β - j) j).eval t := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    have hβ : β - j = β - (j + 1 : ℕ) + 1 := by push_cast; ring
    have h : iteratedDeriv j (fun s : ℝ => exp (-s) * s ^ β) =ᶠ[nhds t] fun s =>
        j.factorial * (exp (-s) * s ^ (β - (j + 1 : ℕ) + 1) *
          (laguerre (β - (j + 1 : ℕ) + 1) j).eval s) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [ih hs, hβ, mul_assoc]
    rw [iteratedDeriv_succ, h.deriv_eq,
      ((hasDerivAt_exp_neg_mul_rpow_mul_laguerre _ j ht).const_mul _).deriv, Nat.factorial_succ]
    push_cast
    ring

/-- The **Rodrigues formula** for the generalized Laguerre polynomials (DLMF 18.5.5 with
Table 18.5.1), as an identity of real functions on `(0, ∞)`:
`Lₙ^{(α)}(x) = x ^ (-α) * exp x / n! * dⁿ/dxⁿ (exp (-x) * x ^ (n + α))`. -/
theorem laguerre_rodrigues (α : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (laguerre α n).eval x =
      x ^ (-α) * exp x / n.factorial *
        iteratedDeriv n (fun t : ℝ => exp (-t) * t ^ ((n : ℝ) + α)) x := by
  rw [iteratedDeriv_exp_neg_mul_rpow_eq_laguerre _ n hx, add_sub_cancel_left, rpow_neg hx.le,
    exp_neg]
  have h₁ : x ^ α ≠ 0 := (rpow_pos_of_pos hx α).ne'
  have h₂ : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  field_simp

end Polynomial
