/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Coordinate-line polynomial degree bounds

Closure properties of functions `f : (ι → R) → R` whose restrictions along coordinate lines
`w ↦ f (Function.update z j w)` agree with polynomials of degree `< d` (`d : WithBot ℕ`).

## Main results

* `TauCeti.exists_degree_lt_and_sub_eq_eval`: subtraction preserves a coordinate-`j` polynomial
  degree bound `< d`.
* `TauCeti.exists_degree_lt_and_add_sum_mul_eval_eq_eval`: adding finite sums
  `∑ a ∈ t, g a z * (P a).eval (z a)` with `j ∉ t` preserves a coordinate-`j` polynomial degree
  bound `< d` when `f₀` and each coefficient function `g a` (`a ∈ t`) already satisfy that bound.
* `TauCeti.exists_degree_lt_and_add_mul_eval_eq_eval`: adding a single term
  `gᵢ z * Pᵢ.eval (z i)` with `i ≠ j` preserves a coordinate-`j` polynomial degree bound `< d`
  when `f₀` and `gᵢ` already satisfy that bound.
-/

public section

open Function
open scoped Polynomial

namespace TauCeti

variable {ι R : Type*} [DecidableEq ι]

/-- Subtraction preserves a coordinate-`j` polynomial degree bound `< d`. -/
theorem exists_degree_lt_and_sub_eq_eval [Ring R] {f g : (ι → R) → R} {j : ι} {d : WithBot ℕ}
    (hf : ∀ z, ∃ Q : R[X], Q.degree < d ∧ ∀ w, f (update z j w) = Q.eval w)
    (hg : ∀ z, ∃ Q : R[X], Q.degree < d ∧ ∀ w, g (update z j w) = Q.eval w) (z : ι → R) :
    ∃ Q : R[X], Q.degree < d ∧ ∀ w, (f - g) (update z j w) = Q.eval w := by
  obtain ⟨n, rfl, hfz⟩ := Polynomial.exists_mem_evalDegreeLT_of_exists_degree_lt (hf z)
  exact Polynomial.mem_evalDegreeLT.mp <|
    (Polynomial.evalDegreeLT R n).sub_mem hfz (Polynomial.mem_evalDegreeLT.mpr (hg z))

/-- Adding finite sums `∑ a ∈ t, g a z * (P a).eval (z a)` preserves a coordinate-`j`
polynomial degree bound `< d` when `f₀` and each coefficient function `g a` (`a ∈ t`) already
satisfy that bound and `j ∉ t`. -/
theorem exists_degree_lt_and_add_sum_mul_eval_eq_eval [CommSemiring R] {f₀ : (ι → R) → R}
    {g : ι → (ι → R) → R} {P : ι → R[X]} {j : ι} {d : WithBot ℕ} {t : Finset ι} (hjt : j ∉ t)
    (hf₀ : ∀ z, ∃ Q : R[X], Q.degree < d ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hg : ∀ a ∈ t, ∀ z, ∃ Q : R[X], Q.degree < d ∧ ∀ w, g a (update z j w) = Q.eval w)
    (z : ι → R) :
    ∃ Q : R[X], Q.degree < d ∧
      ∀ w, f₀ (update z j w) + ∑ a ∈ t, g a (update z j w) * (P a).eval (update z j w a) =
        Q.eval w := by
  obtain ⟨n, rfl, hf₀z⟩ := Polynomial.exists_mem_evalDegreeLT_of_exists_degree_lt (hf₀ z)
  have heq : (fun w ↦ f₀ (update z j w) +
      ∑ a ∈ t, g a (update z j w) * (P a).eval (update z j w a)) =
      (fun w ↦ f₀ (update z j w)) +
        ∑ a ∈ t, (P a).eval (z a) • fun w ↦ g a (update z j w) := by
    ext w
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine congrArg (f₀ (update z j w) + ·) (Finset.sum_congr rfl fun a ha ↦ ?_)
    rw [update_of_ne (fun (h : a = j) ↦ hjt (h ▸ ha)), mul_comm]
  rw [← Polynomial.mem_evalDegreeLT, heq]
  exact (Polynomial.evalDegreeLT R n).add_mem hf₀z
    ((Polynomial.evalDegreeLT R n).sum_mem fun a ha ↦
      (Polynomial.evalDegreeLT R n).smul_mem ((P a).eval (z a))
        (Polynomial.mem_evalDegreeLT.mpr (hg a ha z)))

/-- Adding a single term `gᵢ w * Pᵢ.eval (w i)` with `i ≠ j` preserves a coordinate-`j`
polynomial degree bound `< d` when `f₀` and `gᵢ` already satisfy that bound. -/
theorem exists_degree_lt_and_add_mul_eval_eq_eval [CommSemiring R] {f₀ gᵢ : (ι → R) → R}
    {Pᵢ : R[X]} (i j : ι) (hij : i ≠ j) {d : WithBot ℕ}
    (hf₀ : ∀ z, ∃ Q : R[X], Q.degree < d ∧ ∀ w, f₀ (update z j w) = Q.eval w)
    (hgᵢ : ∀ z, ∃ Q : R[X], Q.degree < d ∧ ∀ w, gᵢ (update z j w) = Q.eval w) (z : ι → R) :
    ∃ Q : R[X], Q.degree < d ∧
      ∀ w, f₀ (update z j w) + gᵢ (update z j w) * Pᵢ.eval (update z j w i) = Q.eval w := by
  simpa only [Finset.sum_singleton] using exists_degree_lt_and_add_sum_mul_eval_eq_eval
    (g := fun _ ↦ gᵢ) (P := fun _ ↦ Pᵢ) (t := {i}) (Finset.notMem_singleton.mpr hij.symm) hf₀
    (fun _ _ ↦ hgᵢ) z

end TauCeti
