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

/-- A homogeneous component is a free module, with the monomials of its degree as basis. -/
instance homogeneousSubmodule_moduleFree {σ R : Type*} [CommSemiring R]
    (n : ℕ) : Module.Free R (homogeneousSubmodule σ R n) := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Free.of_basis (basisRestrictSupport R {d : σ →₀ ℕ | d.degree = n})

/-- The restricted-support basis vector is the monomial indexed by its support element. -/
@[simp]
theorem coe_basisRestrictSupport_apply {σ R : Type*} [CommSemiring R]
    (s : Set (σ →₀ ℕ)) (m : s) :
    ((basisRestrictSupport R s m : restrictSupport R s) : MvPolynomial σ R) =
      monomial m.1 1 := by
  classical
  rw [← (basisRestrictSupport R s).repr_symm_single_one m]
  -- Mathlib defines this basis through `AddMonoidAlgebra.supportedEquivFinsupp`.
  -- Its first equivalence wraps `Finsupp.supportedEquivFinsupp` in `ofCoeff`,
  -- so we expose that representation before simplifying the single basis vector.
  change (((AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) s).symm
    (Finsupp.single m (1 : R)) : restrictSupport R s) : MvPolynomial σ R) = monomial m.1 1
  simp only [AddMonoidAlgebra.supportedEquivFinsupp, LinearEquiv.symm_trans_apply]
  simp [AddMonoidAlgebra.ofCoeff_single, single_eq_monomial]

/-- The monomial basis of a homogeneous component, indexed by exponent vectors of its degree. -/
noncomputable def homogeneousMonomialBasis {σ R : Type*} [CommSemiring R] (n : ℕ) :
    Module.Basis {s : σ →₀ ℕ // s.degree = n} R (homogeneousSubmodule σ R n) :=
  (basisRestrictSupport R {s : σ →₀ ℕ | s.degree = n}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ R n).symm)

/-- A homogeneous monomial basis vector is the corresponding monomial. -/
@[simp]
theorem coe_homogeneousMonomialBasis {σ R : Type*} [CommSemiring R] (n : ℕ)
    (s : {s : σ →₀ ℕ // s.degree = n}) :
    ((homogeneousMonomialBasis (R := R) n s : homogeneousSubmodule σ R n) :
      MvPolynomial σ R) = monomial s.1 1 := by
  simp only [homogeneousMonomialBasis, Module.Basis.map_apply]
  exact coe_basisRestrictSupport_apply {d : σ →₀ ℕ | d.degree = n} s

/-- The coordinate of a homogeneous polynomial in the monomial basis is its corresponding
coefficient. -/
@[simp]
theorem homogeneousMonomialBasis_repr_apply {σ R : Type*} [CommSemiring R] (n : ℕ)
    (p : homogeneousSubmodule σ R n) (s : {s : σ →₀ ℕ // s.degree = n}) :
    (homogeneousMonomialBasis n).repr p s = p.1.coeff s.1 := by
  rfl

/-- The dimension of a homogeneous component is the number of exponent vectors of its degree. -/
theorem finrank_homogeneousSubmodule (σ R : Type*) [CommSemiring R]
    [StrongRankCondition R] (n : ℕ) :
    Module.finrank R (homogeneousSubmodule σ R n) =
      Nat.card (↥{d : σ →₀ ℕ | d.degree = n}) := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis
    (basisRestrictSupport R {d : σ →₀ ℕ | d.degree = n})

/-- The dimension of a homogeneous component is a multichoose number. -/
@[simp]
theorem finrank_homogeneousSubmodule_eq_multichoose (σ R : Type*) [Fintype σ]
    [CommSemiring R] [StrongRankCondition R] (n : ℕ) :
    Module.finrank R (homogeneousSubmodule σ R n) = (Fintype.card σ).multichoose n := by
  classical
  rw [finrank_homogeneousSubmodule]
  let e : (↥{d : σ →₀ ℕ | d.degree = n}) ≃
      (Finset.univ.finsuppAntidiag n : Finset (σ →₀ ℕ)) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun d => by
      simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
  calc
    Nat.card (↥{d : σ →₀ ℕ | d.degree = n}) =
        Nat.card (Finset.univ.finsuppAntidiag n : Finset (σ →₀ ℕ)) := Nat.card_congr e
    _ = (Fintype.card σ).multichoose n := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe,
        Finset.card_finsuppAntidiag_nat_eq_multichoose]
      simp

/-- The degree-`w` homogeneous polynomials in two variables have dimension `w + 1`. -/
theorem finrank_homogeneousSubmodule_fin_two (R : Type*) [CommSemiring R]
    [StrongRankCondition R] (w : ℕ) :
    Module.finrank R (homogeneousSubmodule (Fin 2) R w) = w + 1 := by
  rw [finrank_homogeneousSubmodule_eq_multichoose, Fintype.card_fin, Nat.multichoose_two]

end TauCeti
