/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.Analysis.Complex.MDeriv.Basic
import TauCeti.Analysis.Complex.PartialDeriv.Degree

/-!
# Polynomial degree preservation under mixed partial derivatives

Every mixed partial derivative `TauCeti.mDeriv σ f` of an entire function `f : (Fin n → ℂ) → ℂ`
preserves any strict coordinate polynomial degree bound `Q.degree < d` along any coordinate line
`j` (`TauCeti.exists_degree_lt_and_mDeriv_eq_eval`).
-/

public section

open Finset Function Polynomial

namespace TauCeti

variable {n : ℕ}

/-- Every mixed partial derivative `mDeriv σ f` of an entire function `f` preserves a strict
polynomial degree bound `< d` in any coordinate `j`. -/
theorem exists_degree_lt_and_mDeriv_eq_eval {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (j : Fin n) (σ : Fin n → ℕ) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) :
    ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, mDeriv σ f (update z j w) = Q.eval w := by
  suffices ∀ (s : Finset (Fin n)) (τ : Fin n → ℕ), (∀ i ∉ s, τ i = 0) →
      ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, mDeriv τ f (update z j w) = Q.eval w by
    exact this univ σ (fun i hi ↦ (hi (mem_univ i)).elim)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro τ hτ
    have hτ0 : τ = 0 := by ext i; exact hτ i (notMem_empty i)
    rw [hτ0, mDeriv_zero]
    exact hdeg
  | insert i s _ ih =>
    intro τ hτ
    have hupd : ∀ m ∉ s, update τ i 0 m = 0 := by
      intro m hms
      by_cases hmi : m = i
      · subst hmi; simp
      · simp [hmi, hτ m (fun hm ↦ hms ((mem_insert.mp hm).resolve_left hmi))]
    rw [mDeriv_eq_iterate_partialDeriv_mDeriv_update_zero hf τ i]
    exact exists_degree_lt_and_iterate_partialDeriv_eq_eval
      (differentiable_mDeriv hf (update τ i 0)) i j (ih (update τ i 0) hupd) (τ i)

end TauCeti
