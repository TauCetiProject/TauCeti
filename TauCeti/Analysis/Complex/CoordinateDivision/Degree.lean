/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.Analysis.Complex.CoordinateDivision.Basic
import TauCeti.Analysis.Complex.PartialDeriv.Degree

/-!
# Coordinate polynomial degree bounds for univariate coordinate division

For finite `ι` and an entire scalar function `f : (ι → ℂ) → ℂ`, this file establishes the
coordinate-line polynomial degree bounds for the univariate quotient `TauCeti.partialDivByMonic` and
remainder `TauCeti.partialModByMonic`:

* for monic `P`, every `zᵢ`-line of `partialModByMonic i f P` agrees with a polynomial of degree
  `< P.degree` (`TauCeti.exists_degree_lt_partialModByMonic`);
* `partialDivByMonic i f P` and `partialModByMonic i f P` preserve strict coordinate polynomial
  degree bounds in every other coordinate `j ≠ i`
  (`TauCeti.exists_degree_lt_partialDivByMonic_of_ne`,
  `TauCeti.exists_degree_lt_partialModByMonic_of_ne`).
-/

public section

open Function Polynomial

namespace TauCeti

variable {ι : Type*} [DecidableEq ι] [Finite ι] {f : (ι → ℂ) → ℂ}

/-- **Line polynomial degree of the remainder.** For monic `P` and entire `f : (ι → ℂ) → ℂ`,
every `zᵢ`-line of `partialModByMonic i f P` agrees with a polynomial of degree `< P.degree`. -/
theorem exists_degree_lt_partialModByMonic {P : ℂ[X]} (hP : P.Monic) (hf : Differentiable ℂ f)
    (i : ι) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < P.degree ∧
      ∀ w, partialModByMonic i f P (update z i w) = Q.eval w := by
  rw [degree_eq_natDegree hP.ne_zero]
  exact (iterate_partialDeriv_eq_zero_iff_exists_degree_lt
    (differentiable_partialModByMonic hf i P) i P.natDegree).mp
    (iterate_partialDeriv_partialModByMonic_eq_zero hP hf) z

/-- **Coordinate degree preservation for the quotient.** If `f` is entire and a polynomial of
degree `< d` in another coordinate `j ≠ i`, then so is `partialDivByMonic i f P`. -/
theorem exists_degree_lt_partialDivByMonic_of_ne (hf : Differentiable ℂ f) {i j : ι}
    (hji : j ≠ i) (P : ℂ[X]) {d : WithBot ℕ}
    (hfj : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, partialDivByMonic i f P (update z j w) = Q.eval w :=
  exists_degree_lt_of_comm_iterate_partialDeriv (partialDivByMonic i · P) hf
    (differentiable_partialDivByMonic hf i P)
    (iterate_partialDeriv_partialDivByMonic_of_ne hf hji P) (partialDivByMonic_zero_fun i P)
    hfj z

/-- **Coordinate degree preservation for the remainder.** If `f` is entire and a polynomial of
degree `< d` in another coordinate `j ≠ i`, then so is `partialModByMonic i f P`. -/
theorem exists_degree_lt_partialModByMonic_of_ne (hf : Differentiable ℂ f) {i j : ι}
    (hji : j ≠ i) (P : ℂ[X]) {d : WithBot ℕ}
    (hfj : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, partialModByMonic i f P (update z j w) = Q.eval w :=
  exists_degree_lt_of_comm_iterate_partialDeriv (partialModByMonic i · P) hf
    (differentiable_partialModByMonic hf i P)
    (iterate_partialDeriv_partialModByMonic_of_ne hf hji P) (partialModByMonic_zero_fun i P)
    hfj z

end TauCeti
