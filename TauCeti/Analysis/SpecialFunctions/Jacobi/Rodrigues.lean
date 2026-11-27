/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Jacobi.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.RingTheory.Polynomial.Jacobi.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Polynomial

/-!
# The Rodrigues formula for the Jacobi polynomials

The Jacobi polynomials `Pₙ^{(α,β)} = Polynomial.jacobi α β n` with real parameters are given on the
open interval `(-1, 1)` by the Rodrigues formula (DLMF 18.5.5 with Table 18.5.1)

`Pₙ^{(α,β)}(x) = (-1)ⁿ / (2ⁿ n!) * (1 - x) ^ (-α) * (1 + x) ^ (-β) *
  dⁿ/dxⁿ ((1 - x) ^ (n + α) * (1 + x) ^ (n + β))`.

For general real `α` and `β` the function `(1 - x) ^ (n + α) * (1 + x) ^ (n + β)` is not a
polynomial, so the formula is stated for real functions, with `Real.rpow` powers, on `(-1, 1)`,
where both bases are positive; it is not an identity of polynomials.

The formula follows from a formula for every derivative of `(1 - t) ^ a * (1 + t) ^ b`: for all real
`a`, `b` and `t ∈ (-1, 1)`,

`dʲ/dtʲ ((1 - t) ^ a * (1 + t) ^ b) = (-2)ʲ j! * ((1 - t) ^ (a - j) * (1 + t) ^ (b - j)) *
  P_j^{(a - j, b - j)}(t)`.

It is proved by induction on `j`; the inductive step is the raising relation
`Polynomial.X_sub_one_mul_X_add_one_mul_derivative_jacobi_add_one`. Setting `a = n + α`,
`b = n + β` and `j = n` and cancelling the weight `(1 - t) ^ α * (1 + t) ^ β` gives the Rodrigues
formula. The derivatives of order `j < n` of `(1 - t) ^ (n + α) * (1 + t) ^ (n + β)` are the
boundary terms of the integration by parts behind the Jacobi orthogonality relation: for `-1 < α`
and `-1 < β` the formula shows that each of them extends continuously to `[-1, 1]`, with value `0`
at both endpoints.

## Main statements

* `Polynomial.iteratedDeriv_one_sub_rpow_mul_one_add_rpow_eq_mul_eval_jacobi`: the `j`-th
  derivative of `(1 - t) ^ a * (1 + t) ^ b` on `(-1, 1)`.
* `Polynomial.hasDerivAt_iteratedDeriv_one_sub_rpow_mul_one_add_rpow`: the derivative of that
  `j`-th derivative, at every point of `(-1, 1)`.
* `Polynomial.jacobi_rodrigues`: the Rodrigues formula on `(-1, 1)`.
* `Polynomial.exists_continuousOn_iteratedDeriv_jacobiWeight`: for `-1 < α`, `-1 < β` and
  `j < n`, the `j`-th derivative of `(1 - t) ^ (n + α) * (1 + t) ^ (n + β)` agrees on `(-1, 1)`
  with a function continuous on `[-1, 1]` that vanishes at `±1`.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, 18.5.5 with
  Table 18.5.1, and 18.9.16.
* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, (4.3.1) and (4.10.1).
-/

public section

namespace Polynomial

open Real Set

/-- One step of the derivative formula: on `(-1, 1)`, differentiating
`(1 - t) ^ (γ + 1) * (1 + t) ^ (δ + 1) * P_j^{(γ+1,δ+1)}(t)` lowers both parameters and raises the
index. -/
private theorem hasDerivAt_one_sub_rpow_mul_one_add_rpow_mul_jacobi (γ δ : ℝ) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-1) 1) :
    HasDerivAt
      (fun s : ℝ => (1 - s) ^ (γ + 1) * (1 + s) ^ (δ + 1) * (jacobi (γ + 1) (δ + 1) j).eval s)
      (-(2 * (j + 1)) * ((1 - t) ^ γ * (1 + t) ^ δ) * (jacobi γ δ (j + 1)).eval t) t := by
  have h₁ : 0 < 1 - t := by linarith [ht.2]
  have h₂ : 0 < 1 + t := by linarith [ht.1]
  have hd₁ : HasDerivAt (fun s : ℝ => (1 - s) ^ (γ + 1)) (-(γ + 1) * (1 - t) ^ γ) t := by
    simpa using ((hasDerivAt_id t).const_sub 1).rpow_const (p := γ + 1) (Or.inl h₁.ne')
  have hd₂ : HasDerivAt (fun s : ℝ => (1 + s) ^ (δ + 1)) ((δ + 1) * (1 + t) ^ δ) t := by
    simpa using ((hasDerivAt_id t).const_add 1).rpow_const (p := δ + 1) (Or.inl h₂.ne')
  have h := congrArg (eval t) (X_sub_one_mul_X_add_one_mul_derivative_jacobi_add_one γ δ j)
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_one, eval_C, nsmul_eq_mul, eval_ofNat,
    eval_natCast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  refine ((hd₁.fun_mul hd₂).fun_mul ((jacobi (γ + 1) (δ + 1) j).hasDerivAt t)).congr_deriv ?_
  rw [rpow_add_one h₁.ne', rpow_add_one h₂.ne']
  linear_combination -((1 - t) ^ γ * (1 + t) ^ δ) * h

/-- The inductive step of the derivative formula: if the `j`-th derivative of
`(1 - t) ^ a * (1 + t) ^ b` is given by the formula on `(-1, 1)`, then at every point of `(-1, 1)`
it has the derivative given by the formula of order `j + 1`. -/
private theorem hasDerivAt_iteratedDeriv_one_sub_rpow_mul_one_add_rpow_of_eq (a b : ℝ) (j : ℕ)
    (hj : ∀ s ∈ Ioo (-1 : ℝ) 1,
      iteratedDeriv j (fun s : ℝ => (1 - s) ^ a * (1 + s) ^ b) s =
        (-2) ^ j * j.factorial * ((1 - s) ^ (a - j) * (1 + s) ^ (b - j)) *
          (jacobi (a - j) (b - j) j).eval s)
    {t : ℝ} (ht : t ∈ Ioo (-1) 1) :
    HasDerivAt (iteratedDeriv j (fun s : ℝ => (1 - s) ^ a * (1 + s) ^ b))
      ((-2) ^ (j + 1) * (j + 1).factorial *
        ((1 - t) ^ (a - (j + 1 : ℕ)) * (1 + t) ^ (b - (j + 1 : ℕ))) *
          (jacobi (a - (j + 1 : ℕ)) (b - (j + 1 : ℕ)) (j + 1)).eval t) t := by
  have ha : a - j = a - (j + 1 : ℕ) + 1 := by push_cast; ring
  have hb : b - j = b - (j + 1 : ℕ) + 1 := by push_cast; ring
  have h : iteratedDeriv j (fun s : ℝ => (1 - s) ^ a * (1 + s) ^ b) =ᶠ[nhds t] fun s =>
      (-2) ^ j * j.factorial * ((1 - s) ^ (a - (j + 1 : ℕ) + 1) * (1 + s) ^ (b - (j + 1 : ℕ) + 1) *
        (jacobi (a - (j + 1 : ℕ) + 1) (b - (j + 1 : ℕ) + 1) j).eval s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [hj s hs, ha, hb, mul_assoc]
  refine (((hasDerivAt_one_sub_rpow_mul_one_add_rpow_mul_jacobi _ _ j ht).const_mul _)
    |>.congr_of_eventuallyEq h).congr_deriv ?_
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- The derivatives of `(1 - t) ^ a * (1 + t) ^ b` on `(-1, 1)`, for all real `a` and `b`:
`dʲ/dtʲ ((1 - t) ^ a * (1 + t) ^ b) =
(-2)ʲ j! * ((1 - t) ^ (a - j) * (1 + t) ^ (b - j)) * P_j^{(a - j, b - j)}(t)`.
At `a = n + α`, `b = n + β`, `j = n` it rearranges to the Rodrigues formula
`Polynomial.jacobi_rodrigues`. -/
theorem iteratedDeriv_one_sub_rpow_mul_one_add_rpow_eq_mul_eval_jacobi (a b : ℝ) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-1) 1) :
    iteratedDeriv j (fun s : ℝ => (1 - s) ^ a * (1 + s) ^ b) t =
      (-2) ^ j * j.factorial * ((1 - t) ^ (a - j) * (1 + t) ^ (b - j)) *
        (jacobi (a - j) (b - j) j).eval t := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,
      (hasDerivAt_iteratedDeriv_one_sub_rpow_mul_one_add_rpow_of_eq a b j
        (fun _ hs => ih hs) ht).deriv]

/-- The derivative of the `j`-th derivative of `(1 - t) ^ a * (1 + t) ^ b`: at every
`t ∈ (-1, 1)`, `iteratedDeriv j (fun s => (1 - s) ^ a * (1 + s) ^ b)` has the derivative
`(-2)ʲ⁺¹ (j + 1)! * ((1 - t) ^ (a - (j + 1)) * (1 + t) ^ (b - (j + 1))) *
P_{j+1}^{(a - (j + 1), b - (j + 1))}(t)`. -/
theorem hasDerivAt_iteratedDeriv_one_sub_rpow_mul_one_add_rpow (a b : ℝ) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-1) 1) :
    HasDerivAt (iteratedDeriv j (fun s : ℝ => (1 - s) ^ a * (1 + s) ^ b))
      ((-2) ^ (j + 1) * (j + 1).factorial *
        ((1 - t) ^ (a - (j + 1 : ℕ)) * (1 + t) ^ (b - (j + 1 : ℕ))) *
          (jacobi (a - (j + 1 : ℕ)) (b - (j + 1 : ℕ)) (j + 1)).eval t) t :=
  hasDerivAt_iteratedDeriv_one_sub_rpow_mul_one_add_rpow_of_eq a b j
    (fun _ hs => iteratedDeriv_one_sub_rpow_mul_one_add_rpow_eq_mul_eval_jacobi a b j hs) ht

/-- The **Rodrigues formula** for the Jacobi polynomials (DLMF 18.5.5 with Table 18.5.1), as an
identity of real functions on `(-1, 1)`:
`Pₙ^{(α,β)}(x) = (-1)ⁿ / (2ⁿ n!) * (1 - x) ^ (-α) * (1 + x) ^ (-β) *
dⁿ/dxⁿ ((1 - x) ^ (n + α) * (1 + x) ^ (n + β))`. -/
theorem jacobi_rodrigues (α β : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    (jacobi α β n).eval x =
      (-1) ^ n / (2 ^ n * n.factorial) * (1 - x) ^ (-α) * (1 + x) ^ (-β) *
        iteratedDeriv n (fun t : ℝ => (1 - t) ^ ((n : ℝ) + α) * (1 + t) ^ ((n : ℝ) + β)) x := by
  have h₁ : 0 < 1 - x := by linarith [hx.2]
  have h₂ : 0 < 1 + x := by linarith [hx.1]
  rw [iteratedDeriv_one_sub_rpow_mul_one_add_rpow_eq_mul_eval_jacobi _ _ n hx, add_sub_cancel_left,
    add_sub_cancel_left, rpow_neg h₁.le, rpow_neg h₂.le]
  have h₃ : (1 - x) ^ α ≠ 0 := (rpow_pos_of_pos h₁ α).ne'
  have h₄ : (1 + x) ^ β ≠ 0 := (rpow_pos_of_pos h₂ β).ne'
  have h₅ : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have h₆ : ((-1 : ℝ) ^ n) * (-2) ^ n = 2 ^ n := by rw [← mul_pow]; norm_num
  field_simp
  rw [mul_assoc, h₆]

/-- The boundary terms of the Jacobi orthogonality relation: for `-1 < α`, `-1 < β` and `j < n`,
the `j`-th derivative of `(1 - t) ^ (n + α) * (1 + t) ^ (n + β)` agrees on `(-1, 1)` with a
function that is continuous on `[-1, 1]` and vanishes at `-1` and at `1`. -/
theorem exists_continuousOn_iteratedDeriv_jacobiWeight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {j n : ℕ} (hj : j < n) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc (-1) 1) ∧
      EqOn (iteratedDeriv j fun t : ℝ => (1 - t) ^ ((n : ℝ) + α) * (1 + t) ^ ((n : ℝ) + β)) g
        (Ioo (-1) 1) ∧ g (-1) = 0 ∧ g 1 = 0 := by
  have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  have ha : 0 < (n : ℝ) + α - j := by linarith
  have hb : 0 < (n : ℝ) + β - j := by linarith
  refine ⟨fun t => (-2) ^ j * j.factorial * ((1 - t) ^ ((n : ℝ) + α - j) *
    (1 + t) ^ ((n : ℝ) + β - j)) * (jacobi ((n : ℝ) + α - j) ((n : ℝ) + β - j) j).eval t,
    Continuous.continuousOn ?_, fun t ht =>
      iteratedDeriv_one_sub_rpow_mul_one_add_rpow_eq_mul_eval_jacobi _ _ j ht, ?_, ?_⟩
  · exact (continuous_const.mul (((continuous_const.sub continuous_id).rpow_const
      fun _ => Or.inr ha.le).mul ((continuous_const.add continuous_id).rpow_const
        fun _ => Or.inr hb.le))).mul (Polynomial.continuous _)
  · simp [zero_rpow hb.ne']
  · simp [zero_rpow ha.ne']

end Polynomial
