/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.SpecialFunctions.Airy.Equation
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The product equation of Airy's equation

If `f` and `g` are entire solutions of Airy's equation `w'' = z w`, then their product
`w = f g` solves the third-order linear equation

$$w''' - 4 z w' - 2 w = 0$$

(DLMF 9.11.1). Differentiating this equation `n` times gives
`w^{(n+3)}(z) = 4 z w^{(n+1)}(z) + (4 n + 2) w^{(n)}(z)`, so at the origin the derivatives of
an entire solution satisfy `w^{(n+3)}(0) = (4 n + 2) w^{(n)}(0)`. An entire solution is
therefore determined by `w(0)`, `w'(0)` and `w''(0)`: its Taylor series at the origin is fixed
by them.

## Main results

* `TauCeti.productEquation_mul_of_airy_ode`: the product of two entire solutions of Airy's
  equation solves `w''' - 4 z w' - 2 w = 0` (DLMF 9.11.1).
* `TauCeti.iteratedDeriv_add_three_of_productEquation`: the differentiated equation
  `w^{(n+3)}(z) = 4 z w^{(n+1)}(z) + (4 n + 2) w^{(n)}(z)`.
* `TauCeti.eq_of_productEquation`: two entire solutions with the same `w(0)`, `w'(0)` and
  `w''(0)` are equal.

## References

* NIST Digital Library of Mathematical Functions, §9.11(i), <https://dlmf.nist.gov/9.11.i>.

The proof of DLMF 9.11.1 is adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMFMathlib/Analysis/ODE/SymmetricSquare.lean`
and `DLMF/Airy/Products.lean`; the uniqueness proof is new.
-/

public section

namespace TauCeti

/-- If `f` and `g` are entire solutions of Airy's equation `w'' = z w`, then their product
`w = f g` satisfies `w''' - 4 z w' - 2 w = 0` (DLMF 9.11.1). -/
theorem productEquation_mul_of_airy_ode {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hfe : ∀ z, deriv^[2] f z = z * f z)
    (hge : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    deriv^[3] (fun t => f t * g t) z - 4 * z * deriv (fun t => f t * g t) z -
      2 * (f z * g z) = 0 := by
  have hf' := hasDerivAt_deriv_of_airy_ode hf hfe
  have hg' := hasDerivAt_deriv_of_airy_ode hg hge
  have hd1 : deriv (fun t => f t * g t) = fun t => deriv f t * g t + f t * deriv g t :=
    funext fun t => ((hf t).hasDerivAt.mul (hg t).hasDerivAt).deriv
  have hd2 : deriv (deriv fun t => f t * g t) =
      fun t => 2 * t * (f t * g t) + 2 * (deriv f t * deriv g t) := by
    rw [hd1]
    funext t
    exact (((hf' t).mul (hg t).hasDerivAt).add ((hf t).hasDerivAt.mul (hg' t))).deriv.trans
      (by ring)
  have hd3 : deriv (fun t => 2 * t * (f t * g t) + 2 * (deriv f t * deriv g t)) z =
      2 * (f z * g z) + 4 * z * (deriv f z * g z + f z * deriv g z) :=
    ((((hasDerivAt_id' z).const_mul 2).mul ((hf z).hasDerivAt.mul (hg z).hasDerivAt)).add
      (((hf' z).mul (hg' z)).const_mul 2)).deriv.trans (by rw [Pi.mul_apply]; ring)
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one, hd2, hd1,
    hd3]
  ring

/-- Differentiating `w''' - 4 z w' - 2 w = 0` `n` times: for an entire solution `w`,
`w^{(n+3)}(z) = 4 z w^{(n+1)}(z) + (4 n + 2) w^{(n)}(z)`. -/
theorem iteratedDeriv_add_three_of_productEquation {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hwe : ∀ z, deriv^[3] w z - 4 * z * deriv w z - 2 * w z = 0) (n : ℕ) (z : ℂ) :
    iteratedDeriv (n + 3) w z =
      4 * z * iteratedDeriv (n + 1) w z + (4 * n + 2) * iteratedDeriv n w z := by
  induction n generalizing z with
  | zero =>
    simp only [zero_add, iteratedDeriv_eq_iterate, Function.iterate_one,
      Function.iterate_zero_apply, Nat.cast_zero]
    linear_combination hwe z
  | succ n ih =>
    have hd (k : ℕ) (t : ℂ) : HasDerivAt (iteratedDeriv k w) (iteratedDeriv (k + 1) w t) t := by
      rw [iteratedDeriv_succ]
      exact ((hw.contDiff.differentiable_iteratedDeriv' k) t).hasDerivAt
    rw [Nat.add_right_comm n 1 3, iteratedDeriv_succ, funext ih]
    refine ((((hasDerivAt_id z).const_mul 4).mul (hd (n + 1) z)).add
      ((hd n z).const_mul (4 * (n : ℂ) + 2))).deriv.trans ?_
    simp only [id, Nat.cast_add, Nat.cast_one]
    ring

/-- An entire solution of `w''' - 4 z w' - 2 w = 0` is determined by `w(0)`, `w'(0)` and
`w''(0)` (DLMF §9.11(i)). -/
theorem eq_of_productEquation {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfe : ∀ z, deriv^[3] f z - 4 * z * deriv f z - 2 * f z = 0)
    (hge : ∀ z, deriv^[3] g z - 4 * z * deriv g z - 2 * g z = 0)
    (h₀ : f 0 = g 0) (h₁ : deriv f 0 = deriv g 0) (h₂ : deriv^[2] f 0 = deriv^[2] g 0) :
    f = g := by
  have hsub (n : ℕ) (z : ℂ) : deriv^[n] (f - g) z = deriv^[n] f z - deriv^[n] g z := by
    simp only [← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt
  have hw := hf.sub hg
  have hwe (z : ℂ) : deriv^[3] (f - g) z - 4 * z * deriv (f - g) z - 2 * (f - g) z = 0 := by
    rw [hsub, ← Function.iterate_one deriv, hsub, Function.iterate_one, Pi.sub_apply]
    linear_combination hfe z - hge z
  have h0 (n : ℕ) : iteratedDeriv n (f - g) 0 = 0 := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simp [h₀]
      | 1, _ => rw [iteratedDeriv_eq_iterate, hsub, Function.iterate_one, h₁, sub_self]
      | 2, _ => rw [iteratedDeriv_eq_iterate, hsub, h₂, sub_self]
      | n + 3, ih =>
        rw [iteratedDeriv_add_three_of_productEquation hw hwe, ih n (by omega)]
        ring
  funext z
  rw [← sub_eq_zero, ← Pi.sub_apply, ← Complex.taylorSeries_eq_of_entire' 0 z hw]
  simp [h0]

end TauCeti
