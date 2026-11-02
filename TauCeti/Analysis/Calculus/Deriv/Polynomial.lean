/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Algebra.Polynomial.Taylor

/-!
# Iterated derivatives of polynomial functions and Taylor polynomials of rational functions

The `n`-th derivative of the function `x ↦ p.eval x` is the function of the `n`-th formal
derivative of `p`.

If `Q a ≠ 0`, the rational function `P / Q` is smooth near `a`. Its Taylor polynomial `T` of
order `m` at `a` is characterized algebraically by `T * Q ≡ P` modulo `(X - a) ^ m`. This
congruence is how analytic Taylor coefficients enter polynomial identities, for example the
partial-fraction expansion of a rational function with a pole of order `m` at `a`.

## Main results

* `Polynomial.iteratedDeriv`: the iterated derivative of a polynomial function.
* `Polynomial.X_sub_C_pow_dvd_sub_sum_iteratedDeriv_mul`: `(X - a) ^ m` divides `P - T * Q`,
  where `T` is the order-`m` Taylor polynomial of `P / Q` at `a`.
-/

public section

open Finset Nat

namespace Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The `n`-th derivative of a polynomial function is the function of the `n`-th formal
derivative. -/
@[simp]
protected theorem iteratedDeriv (p : 𝕜[X]) (n : ℕ) :
    iteratedDeriv n (fun x ↦ p.eval x) = fun x ↦ (derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply, ← ih]
    exact congrArg _ (funext fun x ↦ p.deriv)

/-- The `n`-th derivative of a polynomial function at `x` is `n !` times the Hasse derivative of
order `n` at `x`. -/
theorem iteratedDeriv_eq_factorial_mul_eval_hasseDeriv (p : 𝕜[X]) (n : ℕ) (x : 𝕜) :
    iteratedDeriv n (fun x ↦ p.eval x) x = n ! * (hasseDeriv n p).eval x := by
  rw [Polynomial.iteratedDeriv, ← factorial_smul_hasseDeriv]
  simp [nsmul_eq_mul]

variable [CharZero 𝕜]

/-- Let `Q` not vanish at `a`, and let `T` be the Taylor polynomial of order `m` of the rational
function `P / Q` at `a`. Then `T * Q` agrees with `P` to order `m` at `a`. -/
theorem X_sub_C_pow_dvd_sub_sum_iteratedDeriv_mul {P Q : 𝕜[X]} {a : 𝕜} (hQ : Q.eval a ≠ 0)
    (m : ℕ) :
    (X - C a) ^ m ∣ P - (∑ j ∈ range m,
      C (iteratedDeriv j (fun x ↦ P.eval x / Q.eval x) a / j !) * (X - C a) ^ j) * Q := by
  set g : 𝕜 → 𝕜 := fun x ↦ P.eval x / Q.eval x
  have hT (i : ℕ) (hi : i < m) :
      (hasseDeriv i (∑ j ∈ range m, C (iteratedDeriv j g a / j !) * (X - C a) ^ j)).eval a =
        iteratedDeriv i g a / i ! := by
    simp [← smul_eq_C_mul, eval_finsetSum, hi]
  rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
  intro k hk
  rw [taylor_coeff, map_sub, hasseDeriv_mul, eval_sub, eval_finsetSum,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, sub_eq_zero]
  -- Leibniz's rule for `g * Q = P` near `a`, divided by `k !`.
  have hgQ : (g * fun x ↦ Q.eval x) =ᶠ[nhds a] fun x ↦ P.eval x := by
    filter_upwards [Q.differentiable.continuous.continuousAt.eventually_ne hQ] with x hx
    simp [g, div_mul_cancel₀ _ hx]
  have hP : ContDiff 𝕜 k fun x ↦ P.eval x := by simpa using P.contDiff_aeval (𝕜 := 𝕜) k
  have hQ' : ContDiff 𝕜 k fun x ↦ Q.eval x := by simpa using Q.contDiff_aeval (𝕜 := 𝕜) k
  have hg : ContDiffAt 𝕜 k g a := hP.contDiffAt.div hQ'.contDiffAt hQ
  have hL := hgQ.iteratedDeriv_eq k
  rw [← iteratedDerivWithin_univ, iteratedDerivWithin_mul (Set.mem_univ a) uniqueDiffOn_univ
    hg.contDiffWithinAt hQ'.contDiffAt.contDiffWithinAt,
    iteratedDeriv_eq_factorial_mul_eval_hasseDeriv] at hL
  simp only [iteratedDerivWithin_univ, iteratedDeriv_eq_factorial_mul_eval_hasseDeriv] at hL
  rw [← mul_right_inj' (Nat.cast_ne_zero.2 k.factorial_ne_zero : (k ! : 𝕜) ≠ 0), ← hL,
    mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [eval_mul, hT i (by omega), ← Nat.choose_mul_factorial_mul_factorial hik]
  have : (i ! : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
  push_cast
  field_simp

end Polynomial
