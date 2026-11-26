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
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.DividedDifference.Degree
import TauCeti.Analysis.Complex.Liouville

/-!
# Polynomial degree preservation under partial derivatives

Differentiating an entire function `f : (ι → ℂ) → ℂ` along any coordinate `i` (once or iterated
`m` times) preserves strict polynomial degree bounds `Q.degree < d` along every coordinate line `j`.
Along `j = i` this follows from polynomial differentiation, and along `j ≠ i` it follows by
evaluating `partialDslope i f (z i)` on the hyperplane `w i = z i`. Moreover, vanishing of
`(partialDeriv i)^[d] f` characterizes entire functions that agree along every `zᵢ`-line with a
polynomial of degree `< d` (`TauCeti.iterate_partialDeriv_eq_zero_iff_exists_degree_lt`).

## Main results

* `TauCeti.exists_degree_lt_and_partialDeriv_eq_eval`: `partialDeriv i f` preserves any strict
  coordinate polynomial degree bound `< d`.
* `TauCeti.exists_degree_lt_and_iterate_partialDeriv_eq_eval`: `(partialDeriv i)^[m] f` preserves
  any strict coordinate polynomial degree bound `< d`.
* `TauCeti.iterate_partialDeriv_eq_zero_iff_exists_degree_lt`: `(partialDeriv i)^[d] f = 0` iff
  every `zᵢ`-line agrees with a polynomial of degree `< d`.
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
      rw [← partialDslope_of_eq (hf _) (update_of_ne (Ne.symm hij) w z), hQz]⟩

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

/-- **Characterization of coordinate polynomials by iterated partial derivatives.** An entire
function `f : (ι → ℂ) → ℂ` satisfies `∂ᵢ^d f = 0` if and only if along every coordinate line in
`zᵢ`, it agrees with a polynomial of degree `< d`. -/
theorem iterate_partialDeriv_eq_zero_iff_exists_degree_lt {ι : Type*} [DecidableEq ι] [Finite ι]
    {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f) (i : ι) (d : ℕ) :
    (partialDeriv i)^[d] f = 0 ↔
      ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update z i w) = Q.eval w := by
  constructor
  · intro h z
    cases d with
    | zero =>
      refine ⟨0, by simp, fun w ↦ ?_⟩
      simpa using congrFun h (update z i w)
    | succ n =>
      have hline : Differentiable ℂ fun w ↦ f (update z i w) := differentiable_comp_update hf z i
      obtain ⟨Q, hQdeg, hQ⟩ :=
        hline.exists_eq_polynomial_eval_of_iteratedDeriv_eq_zero (n := n) fun k hk ↦ by
          rw [iteratedDeriv_comp_update hf i z k,
            show k = (k - (n + 1)) + (n + 1) by omega, iterate_add_apply, h,
            iterate_fixed (partialDeriv_zero_fun i) _]
          rfl
      refine ⟨Q, (natDegree_le_iff_degree_le.mp hQdeg).trans_lt
        (by exact_mod_cast Nat.lt_succ_self n), fun w ↦ by simpa using congrFun hQ w⟩
  · intro h
    ext z
    cases d with
    | zero =>
      obtain ⟨Q, hQdeg, hQ⟩ := h z
      have hQ0 : Q = 0 := by
        by_contra hne
        exact absurd (zero_le_degree_iff.mpr hne) hQdeg.not_ge
      simpa [hQ0, update_eq_self] using hQ (z i)
    | succ n =>
      obtain ⟨Q, hQdeg, hQ⟩ := h z
      rw [Pi.zero_apply, iterate_partialDeriv_eq_iteratedDeriv_update hf i (n + 1) z]
      have hline : (fun w ↦ f (update z i w)) = Q.eval := funext hQ
      have hQnat : Q.natDegree < n + 1 := by
        rcases eq_or_ne Q 0 with rfl | hQ0
        · simp
        · rw [degree_eq_natDegree hQ0, Nat.cast_lt] at hQdeg
          exact hQdeg
      rw [hline, Polynomial.iteratedDeriv_eq_factorial_mul_eval_hasseDeriv,
        Polynomial.hasseDeriv_eq_zero_of_lt_natDegree Q (n + 1) hQnat, eval_zero, mul_zero]

end TauCeti
