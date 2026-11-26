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

For a general real `α` the function `x ^ (n + α)` is not a polynomial (it is one only when `n + α`
is a natural number), so the formula is stated for real functions, with `Real.rpow` powers, which
cover every real parameter `α` at once, and with the hypothesis `0 < x`; it is not an identity of
polynomials.

The formula follows from a formula for every derivative of `exp (-t) * t ^ β`: for every real `β`
and every `t` with `t ≠ 0` or `j ≤ β`,

`dʲ/dtʲ (exp (-t) * t ^ β) = j! * (exp (-t) * t ^ (β - j)) * L_j^{(β - j)}(t)`.

This identity holds away from the origin, and at the origin when `j ≤ β`. Setting `β = n + α`,
`j = n` gives `dⁿ/dtⁿ (exp (-t) * t ^ (n + α)) = n! * (exp (-t) * t ^ α) * Lₙ^{(α)}(t)`, and the
Rodrigues formula is this identity restricted to `t > 0` (where `t ^ α ≠ 0` and `t ^ (-α)` is its
inverse) and rearranged by cancelling the weight `exp (-t) * t ^ α`. It does not hold at `t = 0`
for every `α`, since `0 ^ (-α) = 0` for `Real.rpow` when `α ≠ 0`.

The derivative formula is proved by induction on `j`; the inductive step is the raising relation
`Polynomial.X_mul_derivative_laguerre_add_one`. The derivatives of order `j < n` of
`exp (-t) * t ^ (n + α)` are the boundary terms of the integration by parts that proves the
Laguerre orthogonality relation, so the general formula is stated for every `j`.

## Main statements

* `Polynomial.hasDerivAt_iteratedDeriv_exp_neg_mul_rpow`: for `t ≠ 0` or `j + 1 ≤ β`, the function
  `iteratedDeriv j (fun s => exp (-s) * s ^ β)` has at `t` the derivative
  `(j + 1)! * (exp (-t) * t ^ (β - (j + 1))) * L_{j+1}^{(β - (j + 1))}(t)`.
* `Polynomial.iteratedDeriv_exp_neg_mul_rpow_eq_mul_eval_laguerre`: for `t ≠ 0` or `j ≤ β`, the
  `j`-th derivative of `exp (-t) * t ^ β` at `t`, as `j! * (exp (-t) * t ^ (β - j))` times the
  value of `L_j^{(β - j)}` at `t`.
* `Polynomial.laguerre_rodrigues`: the Rodrigues formula, for `0 < x` and every real `α`.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, 18.5.5 with
  Table 18.5.1.
* G. Szegő, *Orthogonal Polynomials*, Ch. V, (5.1.5).
-/

public section

namespace Polynomial

open Real

/-- One step of the derivative formula: at every `t ≠ 0`, and at `t = 0` when `0 ≤ γ`,
differentiating `exp (-t) * t ^ (γ + 1) * L_j^{(γ + 1)}(t)` lowers the parameter and raises the
index. -/
private theorem hasDerivAt_exp_neg_mul_rpow_mul_laguerre (γ : ℝ) (j : ℕ) {t : ℝ}
    (ht : t ≠ 0 ∨ 0 ≤ γ) :
    HasDerivAt (fun s : ℝ => exp (-s) * s ^ (γ + 1) * (laguerre (γ + 1) j).eval s)
      ((j + 1) * (exp (-t) * t ^ γ) * (laguerre γ (j + 1)).eval t) t := by
  have h₁ : HasDerivAt (fun s : ℝ => exp (-s)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  have h₂ : HasDerivAt (fun s : ℝ => s ^ (γ + 1)) ((γ + 1) * t ^ γ) t := by
    simpa using hasDerivAt_rpow_const (p := γ + 1) (ht.imp_right fun h => by linarith)
  have h := congrArg (eval t) (X_mul_derivative_laguerre_add_one γ j)
  simp only [eval_mul, eval_X, eval_sub, eval_C, eval_add, eval_one, eval_natCast, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at h
  refine ((h₁.fun_mul h₂).fun_mul ((laguerre (γ + 1) j).hasDerivAt t)).congr_deriv ?_
  have hpow : t ^ (γ + 1) = t ^ γ * t := by
    by_cases ht₀ : t = 0
    · have hγ : 0 ≤ γ := ht.resolve_left (not_not.2 ht₀)
      exact rpow_add_one' (ht₀ ▸ le_rfl) (by linarith)
    · exact rpow_add_one ht₀ γ
  rw [hpow]
  linear_combination (exp (-t) * t ^ γ) * h

/-- The inductive step of the derivative formula: if the `j`-th derivative of
`exp (-t) * t ^ β` is given by the formula at every `s` with `s ≠ 0` or `j ≤ β`, then for `t ≠ 0`
(or `j + 1 ≤ β`) it has at `t` the derivative given by the formula of order `j + 1`. -/
private theorem hasDerivAt_iteratedDeriv_exp_neg_mul_rpow_of_eq (β : ℝ) (j : ℕ)
    (hj : ∀ s : ℝ, s ≠ 0 ∨ (j : ℝ) ≤ β → iteratedDeriv j (fun s : ℝ => exp (-s) * s ^ β) s =
      j.factorial * (exp (-s) * s ^ (β - j)) * (laguerre (β - j) j).eval s)
    {t : ℝ} (ht : t ≠ 0 ∨ ((j + 1 : ℕ) : ℝ) ≤ β) :
    HasDerivAt (iteratedDeriv j (fun s : ℝ => exp (-s) * s ^ β))
      ((j + 1).factorial * (exp (-t) * t ^ (β - (j + 1 : ℕ))) *
        (laguerre (β - (j + 1 : ℕ)) (j + 1)).eval t) t := by
  have hβ : β - j = β - (j + 1 : ℕ) + 1 := by push_cast; ring
  have hev : ∀ᶠ s in nhds t, s ≠ 0 ∨ (j : ℝ) ≤ β := by
    rcases ht with ht | ht
    · filter_upwards [eventually_ne_nhds ht] with s hs using Or.inl hs
    · exact Filter.Eventually.of_forall fun _ => Or.inr (by push_cast at ht; linarith)
  have h : iteratedDeriv j (fun s : ℝ => exp (-s) * s ^ β) =ᶠ[nhds t] fun s =>
      j.factorial * (exp (-s) * s ^ (β - (j + 1 : ℕ) + 1) *
        (laguerre (β - (j + 1 : ℕ) + 1) j).eval s) := by
    filter_upwards [hev] with s hs
    rw [hj s hs, hβ, mul_assoc]
  have hγ : t ≠ 0 ∨ 0 ≤ β - (j + 1 : ℕ) := ht.imp_right fun h => by linarith
  refine (((hasDerivAt_exp_neg_mul_rpow_mul_laguerre _ j hγ).const_mul _).congr_of_eventuallyEq
    h).congr_deriv ?_
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- The derivatives of `exp (-t) * t ^ β`: for real `β` and `t ≠ 0` (or `j ≤ β`, where the
origin is allowed),
`dʲ/dtʲ (exp (-t) * t ^ β) = j! * (exp (-t) * t ^ (β - j)) * L_j^{(β - j)}(t)`.
At `β = n + α`, `j = n` it reads
`dⁿ/dtⁿ (exp (-t) * t ^ (n + α)) = n! * (exp (-t) * t ^ α) * Lₙ^{(α)}(t)`, which rearranges to the
Rodrigues formula `Polynomial.laguerre_rodrigues` only for `t > 0`. -/
theorem iteratedDeriv_exp_neg_mul_rpow_eq_mul_eval_laguerre (β : ℝ) (j : ℕ) {t : ℝ}
    (ht : t ≠ 0 ∨ (j : ℝ) ≤ β) :
    iteratedDeriv j (fun s : ℝ => exp (-s) * s ^ β) t =
      j.factorial * (exp (-t) * t ^ (β - j)) * (laguerre (β - j) j).eval t := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,
      (hasDerivAt_iteratedDeriv_exp_neg_mul_rpow_of_eq β j (fun _ hs => ih hs) ht).deriv]

/-- The derivative of the `j`-th derivative of `exp (-t) * t ^ β`: for real `β` and `t ≠ 0` (or
`j + 1 ≤ β`, where the origin is allowed),
`iteratedDeriv j (fun s => exp (-s) * s ^ β)` has at `t` the derivative
`(j + 1)! * (exp (-t) * t ^ (β - (j + 1))) * L_{j+1}^{(β - (j + 1))}(t)`. It supplies the
derivatives of the boundary terms `dʲ/dtʲ (exp (-t) * t ^ (n + α))`, `j < n`, in the integration by
parts behind the Laguerre orthogonality relation. -/
theorem hasDerivAt_iteratedDeriv_exp_neg_mul_rpow (β : ℝ) (j : ℕ) {t : ℝ}
    (ht : t ≠ 0 ∨ ((j + 1 : ℕ) : ℝ) ≤ β) :
    HasDerivAt (iteratedDeriv j (fun s : ℝ => exp (-s) * s ^ β))
      ((j + 1).factorial * (exp (-t) * t ^ (β - (j + 1 : ℕ))) *
        (laguerre (β - (j + 1 : ℕ)) (j + 1)).eval t) t :=
  hasDerivAt_iteratedDeriv_exp_neg_mul_rpow_of_eq β j
    (fun _ hs => iteratedDeriv_exp_neg_mul_rpow_eq_mul_eval_laguerre β j hs) ht

/-- The **Rodrigues formula** for the generalized Laguerre polynomials (DLMF 18.5.5 with
Table 18.5.1), as an identity of real functions on `(0, ∞)`:
`Lₙ^{(α)}(x) = x ^ (-α) * exp x / n! * dⁿ/dxⁿ (exp (-x) * x ^ (n + α))`. It is the
case `β = n + α`, `j = n` of `Polynomial.iteratedDeriv_exp_neg_mul_rpow_eq_mul_eval_laguerre` for
`x > 0`, after multiplying by `x ^ (-α) * exp x` to cancel the weight; the hypothesis `0 < x` is
needed (at `x = 0`, `α = 1`, `n = 0` the left side is `1` and the right side is `0`). -/
theorem laguerre_rodrigues (α : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (laguerre α n).eval x =
      x ^ (-α) * exp x / n.factorial *
        iteratedDeriv n (fun t : ℝ => exp (-t) * t ^ ((n : ℝ) + α)) x := by
  rw [iteratedDeriv_exp_neg_mul_rpow_eq_mul_eval_laguerre _ n (Or.inl hx.ne'), add_sub_cancel_left,
    rpow_neg hx.le, exp_neg]
  have h₁ : x ^ α ≠ 0 := (rpow_pos_of_pos hx α).ne'
  have h₂ : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  field_simp

end Polynomial
