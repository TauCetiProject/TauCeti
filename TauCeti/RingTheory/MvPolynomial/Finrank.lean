/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of homogeneous polynomials

The monomial basis of a homogeneous component is indexed by exponent vectors of its degree.
For two variables this gives dimension `w + 1`, used for the scalar-matrix trace on binary forms.
-/

public section

namespace TauCeti

open MvPolynomial

/-- A homogeneous component in finitely many variables is a finite module. -/
instance homogeneousSubmodule_moduleFinite {σ R : Type*} [CommSemiring R] [Finite σ]
    (n : ℕ) : Module.Finite R (homogeneousSubmodule σ R n) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg σ R n)

/-- The dimension of a homogeneous component is the number of exponent vectors of its degree. -/
theorem finrank_homogeneousSubmodule (σ R : Type*) [Finite σ] [CommSemiring R]
    [StrongRankCondition R] (n : ℕ) :
    Module.finrank R (homogeneousSubmodule σ R n) =
      Nat.card (↥{d : σ →₀ ℕ | d.degree = n}) := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have : Fintype (↥{d : σ →₀ ℕ | d.degree = n}) :=
    Set.Finite.fintype (Finsupp.finite_of_degree_eq n)
  exact (Module.finrank_eq_card_basis
    (basisRestrictSupport R {d : σ →₀ ℕ | d.degree = n})).trans
      (Nat.card_eq_fintype_card (α := ↥{d : σ →₀ ℕ | d.degree = n})).symm

/-- The degree-`w` homogeneous polynomials in two variables have dimension `w + 1`. -/
theorem finrank_homogeneousSubmodule_fin_two (R : Type*) [CommSemiring R]
    [StrongRankCondition R] (w : ℕ) :
    Module.finrank R (homogeneousSubmodule (Fin 2) R w) = w + 1 := by
  classical
  rw [finrank_homogeneousSubmodule]
  let e : (↥{d : Fin 2 →₀ ℕ | d.degree = w}) ≃
      (Finset.univ.finsuppAntidiag w : Finset (Fin 2 →₀ ℕ)) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun d => by
      rw [Finset.mem_finsuppAntidiag]
      simp only [Finset.subset_univ, and_true]
      change d.degree = w ↔ (∑ i : Fin 2, d i) = w
      rw [Finsupp.degree_eq_sum])
  calc
    Nat.card (↥{d : Fin 2 →₀ ℕ | d.degree = w}) =
        Nat.card (Finset.univ.finsuppAntidiag w : Finset (Fin 2 →₀ ℕ)) := Nat.card_congr e
    _ = w + 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe,
        Finset.card_finsuppAntidiag_nat_eq_multichoose]
      simp

end TauCeti
