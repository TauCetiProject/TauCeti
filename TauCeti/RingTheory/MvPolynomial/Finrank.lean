/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of binary homogeneous polynomials

A binary monomial of degree `w` has exponent pair in the natural-number antidiagonal of `w`.
Thus the homogeneous component in two variables has dimension `w + 1`. This count is used for
the scalar-matrix trace on binary forms.
-/

public section

namespace TauCeti

open MvPolynomial

/-- The degree-`w` homogeneous polynomials in two variables have dimension `w + 1`. -/
theorem finrank_binaryForms (K : Type*) [Field K] (w : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin 2) K w) = w + 1 := by
  have hdegree (d : Fin 2 →₀ ℕ) :
      d.degree = ((finTwoArrowEquiv' ℕ) d).1 + ((finTwoArrowEquiv' ℕ) d).2 := by
    rw [Finsupp.degree_eq_sum, ← Finsupp.sum_fintype d (fun _ n => n) (by simp)]
    simpa only [Equiv.symm_apply_apply] using
      (finTwoArrowEquiv'_sum_eq (d := (finTwoArrowEquiv' ℕ) d))
  let e : {d : Fin 2 →₀ ℕ // d.degree = w} ≃ Finset.antidiagonal w :=
    Equiv.subtypeEquiv (finTwoArrowEquiv' ℕ) (fun d => by
      rw [Finset.mem_antidiagonal, ← hdegree])
  let : Fintype {d : Fin 2 →₀ ℕ // d.degree = w} := Fintype.ofEquiv _ e.symm
  let f : homogeneousSubmodule (Fin 2) K w ≃ₗ[K]
      {d : Fin 2 →₀ ℕ // d.degree = w} →₀ K :=
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported (Fin 2) K w)) ≪≫ₗ
      AddMonoidAlgebra.supportedEquivFinsupp {d : Fin 2 →₀ ℕ | d.degree = w}
  rw [f.finrank_eq, Module.finrank_finsupp_self]
  exact (Fintype.card_congr e).trans (by simp [Finset.Nat.card_antidiagonal])

end TauCeti
