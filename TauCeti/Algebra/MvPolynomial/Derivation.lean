/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Coefficientwise derivations of multivariate polynomials

Let `A` be a commutative `R`-algebra. An `R`-derivation `d` of `A` acts on `MvPolynomial σ A`
coefficient by coefficient; `Derivation.mvMapCoeffs d` is this `R`-derivation, which kills the
variables. It is the multivariate analogue of Mathlib's `Derivation.mapCoeffs`. Adding an
`A`-linear derivation `MvPolynomial.mkDerivation A f`, with scalars restricted to `R`, gives an
`R`-derivation of `MvPolynomial σ A` lifting `d` with prescribed values `f` on the variables.

`MvPolynomial.derivation_ext'` records that an `R`-derivation of `MvPolynomial σ A` is
determined by its values on the constants and on the variables. Mathlib's
`MvPolynomial.derivation_ext` covers derivations that are linear over the coefficient ring,
which vanish on constants.
-/

public section

noncomputable section

open MvPolynomial

variable {R A σ : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

namespace MvPolynomial

/-- An `R`-derivation of `MvPolynomial σ A` is determined by its values on the constants `C a`
and on the variables `X i`. -/
theorem derivation_ext' {M : Type*} [AddCommMonoid M] [Module (MvPolynomial σ A) M] [Module R M]
    {D₁ D₂ : Derivation R (MvPolynomial σ A) M}
    (hC : ∀ a, D₁ (C a) = D₂ (C a)) (hX : ∀ i, D₁ (X i) = D₂ (X i)) : D₁ = D₂ := by
  ext p
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [Derivation.leibniz, Derivation.leibniz, hp, hX]

end MvPolynomial

namespace Derivation

variable (d : Derivation R A A)

/-- Mapping the coefficients of a monomial along a derivation. -/
private theorem addMonoidAlgebraMap_monomial (m : σ →₀ ℕ) (a : A) :
    AddMonoidAlgebra.map (d : A →ₗ[R] A).toAddMonoidHom (monomial m a : MvPolynomial σ A) =
      monomial m (d a) := by
  classical
  ext n
  simp [coeff_monomial, apply_ite d]

/-- The `R`-derivation of `MvPolynomial σ A` applying the derivation `d` of `A` to every
coefficient. -/
def mvMapCoeffs : Derivation R (MvPolynomial σ A) (MvPolynomial σ A) where
  toFun := AddMonoidAlgebra.map (d : A →ₗ[R] A).toAddMonoidHom
  map_add' := AddMonoidAlgebra.map_add _
  map_smul' r p := by
    ext m
    rw [coeff_addMonoidAlgebraMap, coeff_smul, coeff_smul, coeff_addMonoidAlgebraMap]
    exact d.map_smul r _
  map_one_eq_zero' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← C_1, C_apply, addMonoidAlgebraMap_monomial, map_one_eq_zero, monomial_zero]
  leibniz' p q := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    -- Both sides are biadditive in `p` and `q`, so it suffices to compare monomials.
    induction p using MvPolynomial.induction_on' with
    | add p p' hp hp' =>
      simp only [add_mul, AddMonoidAlgebra.map_add, hp, hp', add_smul, smul_add]
      abel
    | monomial m a =>
      induction q using MvPolynomial.induction_on' with
      | add q q' hq hq' =>
        simp only [mul_add, AddMonoidAlgebra.map_add, hq, hq', add_smul, smul_add]
        abel
      | monomial n b =>
        simp only [monomial_mul_monomial, addMonoidAlgebraMap_monomial, Derivation.leibniz,
          smul_eq_mul, map_add]
        rw [add_comm n m]

/-- The coefficients of `d.mvMapCoeffs p` are the derivatives of those of `p`. -/
@[simp]
theorem coeff_mvMapCoeffs (p : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (d.mvMapCoeffs p).coeff m = d (p.coeff m) :=
  coeff_addMonoidAlgebraMap _ p m

/-- `d.mvMapCoeffs` differentiates the coefficient of a monomial. -/
@[simp]
theorem mvMapCoeffs_monomial (m : σ →₀ ℕ) (a : A) :
    d.mvMapCoeffs (monomial m a : MvPolynomial σ A) = monomial m (d a) :=
  addMonoidAlgebraMap_monomial d m a

/-- `d.mvMapCoeffs` acts on constants by `d`. -/
@[simp]
theorem mvMapCoeffs_C (a : A) : d.mvMapCoeffs (C a : MvPolynomial σ A) = C (d a) :=
  d.mvMapCoeffs_monomial 0 a

/-- `d.mvMapCoeffs` kills the variables. -/
@[simp]
theorem mvMapCoeffs_X (i : σ) : d.mvMapCoeffs (X i : MvPolynomial σ A) = 0 := by
  rw [X, mvMapCoeffs_monomial, map_one_eq_zero, map_zero]

end Derivation
