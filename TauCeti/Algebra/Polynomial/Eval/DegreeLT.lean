/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.Algebra.Polynomial.Eval.Linear

/-!
# Evaluation submodule for polynomials of bounded degree

This file defines `Polynomial.evalDegreeLT R n`, the `R`-submodule of functions `R → R` obtained
by evaluating polynomials in Mathlib's `Polynomial.degreeLT R n` (i.e. polynomials of degree `< n`),
together with membership characterizations and extraction of `n : ℕ` from a `WithBot ℕ` degree
bound.

## Main definitions and results

* `Polynomial.evalDegreeLT`: the `R`-submodule of functions `R → R` represented by polynomials of
  degree `< n`.
* `Polynomial.evalDegreeLT_def`: defining formula `(degreeLT R n).map (evalLinearMap R)`.
* `Polynomial.mem_evalDegreeLT`: `f ∈ evalDegreeLT R n ↔ ∃ Q, Q.degree < n ∧ ∀ w, f w = Q.eval w`.
* `Polynomial.mem_evalDegreeLT_natDegree_iff`: membership in `evalDegreeLT R g.natDegree` for
  `g ≠ 0`.
* `Polynomial.exists_mem_evalDegreeLT_of_exists_degree_lt`: extracting `n : ℕ` and membership in
  `evalDegreeLT R n` from a `WithBot ℕ` degree bound.
-/

public section

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] {g : R[X]}

/-- The `R`-submodule of functions `R → R` induced by evaluating polynomials of degree `< n`. -/
noncomputable def evalDegreeLT (R : Type*) [Semiring R] (n : ℕ) : Submodule R (R → R) :=
  (degreeLT R n).map (evalLinearMap R)

/-- Defining formula for `evalDegreeLT` as the image of `degreeLT R n` under
`evalLinearMap R`. -/
theorem evalDegreeLT_def (R : Type*) [Semiring R] (n : ℕ) :
    evalDegreeLT R n = (degreeLT R n).map (evalLinearMap R) := (rfl)

/-- A function `R → R` lies in `evalDegreeLT R n` iff it is evaluation of some polynomial of
degree `< n`. -/
theorem mem_evalDegreeLT {n : ℕ} {f : R → R} :
    f ∈ evalDegreeLT R n ↔ ∃ Q : R[X], Q.degree < n ∧ ∀ w, f w = Q.eval w := by
  simp only [evalDegreeLT, Submodule.mem_map, mem_degreeLT, funext_iff, evalLinearMap_apply]
  refine exists_congr fun Q ↦ and_congr_right fun _ ↦ forall_congr' fun _ ↦ eq_comm

/-- A function `R → R` lies in `evalDegreeLT R g.natDegree` iff it is evaluation of a polynomial of
degree `< g.degree`, for `g ≠ 0`. -/
theorem mem_evalDegreeLT_natDegree_iff (hg : g ≠ 0) {f : R → R} :
    f ∈ evalDegreeLT R g.natDegree ↔ ∃ Q : R[X], Q.degree < g.degree ∧ ∀ w, f w = Q.eval w := by
  rw [mem_evalDegreeLT, degree_eq_natDegree hg]

/-- If `f` agrees with some polynomial of degree `< d` (`d : WithBot ℕ`), then `d = (n : ℕ)` and
`f ∈ evalDegreeLT R n`. -/
theorem exists_mem_evalDegreeLT_of_exists_degree_lt {d : WithBot ℕ} {f : R → R}
    (h : ∃ Q : R[X], Q.degree < d ∧ ∀ w, f w = Q.eval w) :
    ∃ n : ℕ, d = n ∧ f ∈ evalDegreeLT R n := by
  obtain ⟨Q, hQ, hfe⟩ := h
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp (bot_le.trans_lt hQ).ne'
  have hdn : d = n := by rw [← hn, Nat.cast_withBot]
  exact ⟨n, hdn, mem_evalDegreeLT.mpr ⟨Q, hdn ▸ hQ, hfe⟩⟩

end Semiring

end Polynomial
