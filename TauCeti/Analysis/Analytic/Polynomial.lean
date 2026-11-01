/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Substituting an analytic function into a polynomial relation

For a polynomial `P` whose coefficients are multivariate polynomials, and a function `f`, the
expression `P (y, f y)` is obtained by evaluating the coefficients at `y` and the variable at
`f y`. This file shows that it is analytic when `f` is, so that such a relation, once satisfied
near one point of a preconnected set on which `f` is analytic, holds on the whole set.

* `AnalyticOnNhd.eval_map_eval`: substituting an analytic function into a polynomial with
  polynomial coefficients gives an analytic function.
* `AnalyticOnNhd.eval_map_eval_eq_zero_of_isPreconnected`: analytic continuation of a
  polynomial relation along a preconnected set.
-/

public section

open Polynomial Set Topology

variable {𝕜 σ : Type*} [NontriviallyNormedField 𝕜] [Fintype σ] {f : (σ → 𝕜) → 𝕜}
  {s : Set (σ → 𝕜)}

/-- Substituting an analytic function into a polynomial with polynomial coefficients gives an
analytic function. -/
theorem AnalyticOnNhd.eval_map_eval (hf : AnalyticOnNhd 𝕜 f s) (P : (MvPolynomial σ 𝕜)[X]) :
    AnalyticOnNhd 𝕜 (fun y ↦ (P.map (MvPolynomial.eval y)).eval (f y)) s := by
  have hcoeff (p : MvPolynomial σ 𝕜) : AnalyticOnNhd 𝕜 (fun y ↦ MvPolynomial.eval y p) s :=
    (AnalyticOnNhd.eval_continuousLinearMap (.id 𝕜 (σ → 𝕜)) p).mono (subset_univ s)
  simp_rw [eval_map, eval₂_eq_sum_range]
  exact Finset.analyticOnNhd_fun_sum _ fun i _ ↦ (hcoeff (P.coeff i)).mul (hf.pow i)

/-- **Analytic continuation of a polynomial relation.** If `f` is analytic on a preconnected set
`s` and satisfies the relation `P (y, f y) = 0` near one point of `s`, it satisfies this relation
at every point of `s`. -/
theorem AnalyticOnNhd.eval_map_eval_eq_zero_of_isPreconnected (hf : AnalyticOnNhd 𝕜 f s)
    (hs : IsPreconnected s) {P : (MvPolynomial σ 𝕜)[X]} {x : σ → 𝕜} (hx : x ∈ s)
    (hP : ∀ᶠ y in 𝓝 x, (P.map (MvPolynomial.eval y)).eval (f y) = 0) :
    ∀ y ∈ s, (P.map (MvPolynomial.eval y)).eval (f y) = 0 :=
  fun _ hy ↦ (hf.eval_map_eval P).eqOn_zero_of_preconnected_of_eventuallyEq_zero hs hx hP hy
