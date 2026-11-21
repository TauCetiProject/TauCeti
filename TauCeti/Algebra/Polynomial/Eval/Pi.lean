/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial evaluation over products

Polynomial evaluation commutes with projection to each coordinate of a product of
semirings. This lets coordinatewise arguments use `Polynomial.eval_map_apply`
without folding function application back into a ring homomorphism.

Also, fixing one coordinate of a function `(ι → R) → R` preserves polynomial degree bounds along
every coordinate slice (and turns slices along the fixed coordinate into constant polynomials).
-/

public section

namespace Polynomial

/-- Evaluating a polynomial over a product commutes with projection to a coordinate. -/
@[simp] theorem eval_map_evalRingHom {ι : Type*} {R : ι → Type*}
    [∀ i, Semiring (R i)] (p : (∀ i, R i)[X]) (x : ∀ i, R i) (i : ι) :
    (p.map (Pi.evalRingHom R i)).eval (x i) = p.eval x i := by
  simpa only [Pi.evalRingHom_apply] using p.eval_map_apply (Pi.evalRingHom R i) x

end Polynomial

namespace TauCeti

open Polynomial

/-- Fixing the `i`-th coordinate at `ζ` preserves a strict polynomial degree bound `< d` in any
coordinate `j` (becoming constant in coordinate `i` itself). -/
theorem exists_degree_lt_and_update_eq_eval {ι R : Type*} [DecidableEq ι] [Semiring R]
    {f : (ι → R) → R} (i j : ι) (ζ : R) {d : WithBot ℕ}
    (hf : ∀ y, ∃ Q : R[X], Q.degree < d ∧ ∀ w, f (Function.update y j w) = Q.eval w)
    (z : ι → R) :
    ∃ Q : R[X], Q.degree < d ∧
      ∀ w, f (Function.update (Function.update z j w) i ζ) = Q.eval w := by
  by_cases hij : j = i
  · subst hij
    obtain ⟨Q, hQdeg, hQ⟩ := hf z
    refine ⟨C (Q.eval ζ), ?_, fun w ↦ by simp [hQ ζ]⟩
    rcases eq_or_ne Q 0 with rfl | hQ0
    · simpa using hQdeg
    · exact degree_C_le.trans_lt ((zero_le_degree_iff.mpr hQ0).trans_lt hQdeg)
  · obtain ⟨Q, hQdeg, hQ⟩ := hf (Function.update z i ζ)
    exact ⟨Q, hQdeg, fun w ↦ by rw [Function.update_comm hij, hQ]⟩

/-- Fixing the `i`-th coordinate at `ζ` preserves a polynomial degree bound `≤ e` in any
coordinate `j` (becoming constant in coordinate `i` itself). -/
theorem exists_natDegree_le_and_update_eq_eval {ι R : Type*} [DecidableEq ι] [Semiring R]
    {f : (ι → R) → R} (i j : ι) (ζ : R) {e : ℕ}
    (hf : ∀ y, ∃ Q : R[X], Q.natDegree ≤ e ∧ ∀ w, f (Function.update y j w) = Q.eval w)
    (z : ι → R) :
    ∃ Q : R[X], Q.natDegree ≤ e ∧
      ∀ w, f (Function.update (Function.update z j w) i ζ) = Q.eval w := by
  simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using
    exists_degree_lt_and_update_eq_eval i j ζ (d := Order.succ (e : WithBot ℕ))
      (fun y ↦ by simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using hf y) z

end TauCeti
