/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.LeftRegular
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul
public import TauCeti.Algebra.Coalgebra.Comodule.SymmetricAlgebra.Polynomial

/-!
# Orbit coordinates intertwine coactions

The orbit coordinates `TauCeti.Comodule.orbitCoordinates m` of a vector `m` pull a polynomial
function `f` on a comodule `V` back to the function `g ↦ f(g m)` on the group. This file proves
that this pullback is equivariant scheme-theoretically: it intertwines the contragredient
coaction on polynomial functions, `TauCeti.Comodule.polynomial`, with left translation on the
group, the coaction `TauCeti.Comodule.leftRegular`. The base-valued-point shadow of this
statement is `TauCeti.Comodule.leftTranslationAlgEquiv_comp_orbitCoordinates`.

The statement is made in the coordinates of a finite basis `b`, where the polynomial functions are
`MvPolynomial ι R` and the orbit coordinates send `X i` to the matrix coefficient `c(b*ᵢ, m)`.

## Main declarations

* `TauCeti.Comodule.polynomialOrbitCoordinates`: the orbit coordinates in the coordinates of a
  basis.
* `TauCeti.Comodule.leftRegularCoactAlgHom_comp_polynomialOrbitCoordinates`: the orbit
  coordinates intertwine the coaction on polynomial functions with the left regular coaction.
* `TauCeti.Comodule.map_polynomialOrbitCoordinates_comp_polynomialCoact`: the same, as the
  equation of linear maps required of a comodule morphism.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.2.7.
-/

public section

open Module

namespace TauCeti.Comodule

variable {R H V ι : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V] [Fintype ι] [DecidableEq ι]

variable (H) in
/-- The orbit coordinates of a vector `m` in the coordinates of a basis `b`: the algebra
homomorphism `MvPolynomial ι R →ₐ[R] H` sending `X i` to the matrix coefficient `c(b*ᵢ, m)`.
On points it sends a polynomial function `f` to the function `g ↦ f(g m)`. -/
noncomputable def polynomialOrbitCoordinates (b : Basis ι R V) (m : V) :
    MvPolynomial ι R →ₐ[R] H :=
  (orbitCoordinates m).comp (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.toAlgHom

@[simp]
theorem polynomialOrbitCoordinates_X (b : Basis ι R V) (m : V) (i : ι) :
    polynomialOrbitCoordinates H b m (MvPolynomial.X i) =
      matrixCoefficient (C := H) (b.coord i) m := by
  simp [polynomialOrbitCoordinates]

/-- **Orbit coordinates are equivariant.** Pulling polynomial functions back along the orbit map
`g ↦ g m` intertwines the coaction on polynomial functions on `V`, the contragredient action
`(g • f)(v) = f(g⁻¹ v)`, with the left regular coaction, left translation `φ ↦ φ(g⁻¹ ·)`. -/
theorem leftRegularCoactAlgHom_comp_polynomialOrbitCoordinates (b : Basis ι R V) (m : V) :
    (leftRegularCoactAlgHom R H).comp (polynomialOrbitCoordinates H b m) =
      (Algebra.TensorProduct.map (polynomialOrbitCoordinates H b m) (AlgHom.id R H)).comp
        (polynomialCoact H b) := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [leftRegularCoact_apply, comul_matrixCoefficient_eq_sum (C := H) b, polynomialCoact_X]

/-- **Orbit coordinates are equivariant**, as linear maps: the form of
`leftRegularCoactAlgHom_comp_polynomialOrbitCoordinates` taken by the `map_coact` field of a
comodule morphism from `polynomial H b` to the left regular comodule `leftRegular R H`. -/
theorem map_polynomialOrbitCoordinates_comp_polynomialCoact (b : Basis ι R V) (m : V) :
    TensorProduct.map (polynomialOrbitCoordinates H b m).toLinearMap LinearMap.id ∘ₗ
        (polynomialCoact H b).toLinearMap =
      leftRegularCoact R H ∘ₗ (polynomialOrbitCoordinates H b m).toLinearMap := by
  have h := congrArg AlgHom.toLinearMap
    (leftRegularCoactAlgHom_comp_polynomialOrbitCoordinates (H := H) b m)
  simp only [AlgHom.comp_toLinearMap, toLinearMap_leftRegularCoactAlgHom,
    Algebra.TensorProduct.toLinearMap_map, TensorProduct.AlgebraTensorModule.map_eq,
    AlgHom.toLinearMap_id] at h
  exact h.symm

end TauCeti.Comodule
