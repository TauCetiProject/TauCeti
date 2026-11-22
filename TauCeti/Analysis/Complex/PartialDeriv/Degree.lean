/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.Analysis.Complex.PartialDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.DividedDifference.Degree

/-!
# Polynomial degree preservation under partial derivatives

Differentiating an entire function `f : (ι → ℂ) → ℂ` along any coordinate `i` (once or iterated
`m` times) preserves strict polynomial degree bounds `Q.degree < d` along every coordinate line `j`.
Along `j = i` this follows from polynomial differentiation, and along `j ≠ i` it follows by
evaluating `partialDslope i (z i) f` on the hyperplane `w i = z i`.

## Main results

* `TauCeti.exists_degree_lt_and_partialDeriv_eq_eval`: `partialDeriv i f` preserves any strict
  coordinate polynomial degree bound `< d`.
* `TauCeti.exists_degree_lt_and_iterate_partialDeriv_eq_eval`: `(partialDeriv i)^[m] f` preserves
  any strict coordinate polynomial degree bound `< d`.
-/

public section

open Function Polynomial

namespace TauCeti

/-- Differentiating an entire function along coordinate `i` preserves a strict polynomial degree
bound `< d` in every coordinate `j`. -/
theorem exists_degree_lt_and_partialDeriv_eq_eval {ι : Type*} [DecidableEq ι] [Finite ι]
    {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f) (i j : ι) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, partialDeriv i f (update z j w) = Q.eval w := by
  by_cases hij : j = i
  · subst hij
    obtain ⟨Q, hQdeg, hQ⟩ := hdeg z
    refine ⟨Q.derivative, degree_derivative_le.trans_lt hQdeg, fun w ↦ ?_⟩
    rw [partialDeriv_eq_deriv_update (hf _) j, update_self]
    have hfun : (fun s ↦ f (update (update z j w) j s)) = fun s ↦ Q.eval s :=
      funext fun s ↦ by simp [hQ]
    rw [hfun, Polynomial.deriv]
  · obtain ⟨Q, hQ, hQz⟩ := exists_degree_lt_and_partialDslope_eq_eval hf i j (z i) hdeg z
    exact ⟨Q, hQ, fun w ↦ by
      rw [← partialDslope_of_eq (hf _) i (update_of_ne (Ne.symm hij) w z), hQz]⟩

/-- Iterated differentiation of an entire function along coordinate `i` preserves a strict
polynomial degree bound `< d` in every coordinate `j`. -/
theorem exists_degree_lt_and_iterate_partialDeriv_eq_eval {ι : Type*} [DecidableEq ι] [Finite ι]
    {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f) (i j : ι) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (m : ℕ) :
    ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧
      ∀ w, (partialDeriv i)^[m] f (update z j w) = Q.eval w := by
  induction m with
  | zero => exact hdeg
  | succ m ih =>
    simp_rw [iterate_succ_apply']
    exact exists_degree_lt_and_partialDeriv_eq_eval (differentiable_iterate_partialDeriv hf i m)
      i j ih

end TauCeti
