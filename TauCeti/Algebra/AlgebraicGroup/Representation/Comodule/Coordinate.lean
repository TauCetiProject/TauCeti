/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Comodule structures and coordinate representation maps

For a module with a specified finite basis, right comodule structures over a commutative
Hopf algebra `H` correspond to Hopf algebra maps `O(GLₙ) → H`. The inverse corestricts the
standard comodule of `GLₙ` and transports it along the basis identification. Both inverse
identities hold over arbitrary commutative base rings, including in rank zero.

This uses `TauCeti.Comodule.coordinateBialgHom`, `TauCeti.GeneralLinear.standardComodule`
and transport of comodules along linear equivalences.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a), especially Remark 4.1.
-/

public section

open TauCeti
open scoped TensorProduct

namespace Module.Basis

universe u v w

variable {R : Type u} {H : Type v} {M : Type w} {n : ℕ}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M]

/-- The comodule associated to a coordinate representation map, expressed in the basis `b`. -/
@[instance_reducible]
noncomputable def comoduleOfCoordinateBialgHom (b : Basis (Fin n) R M)
    (f : GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H) : Comodule R H M :=
  let := GeneralLinear.corestrictStandardComodule R n f
  Comodule.Transport b.equivFun.symm

/-- The recovered coaction sends a basis vector to the corresponding column of the image
of the generic matrix. -/
-- Generic transport and corestriction simp rules already expand this coaction.
theorem comoduleOfCoordinateBialgHom_coact_basis (b : Basis (Fin n) R M)
    (f : GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H) (j : Fin n) :
    (b.comoduleOfCoordinateBialgHom f).coact (b j) =
      ∑ i, b i ⊗ₜ[R] f (GeneralLinear.genericMatrix R n i j) := by
  classical
  let : Comodule R H (Fin n → R) := GeneralLinear.corestrictStandardComodule R n f
  rw [comoduleOfCoordinateBialgHom, Comodule.transport_coact_apply, LinearEquiv.symm_symm]
  have hj : b.equivFun (b j) = (Pi.basisFun R (Fin n)) j := by
    ext i
    simp [Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [hj]
  let := GeneralLinear.standardComodule R n
  rw [Comodule.corestrict_coact_apply, GeneralLinear.standardComodule_coact, Pi.basisFun_apply,
    GeneralLinear.standardCoact_apply_basisFun]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe]
  congr 1
  funext i
  simp [GeneralLinear.genericMatrix_apply, BialgHom.toCoalgHom_apply]

/-- The coefficient matrix of the recovered comodule is the image of the generic matrix. -/
@[simp]
theorem coefficientMatrix_comoduleOfCoordinateBialgHom (b : Basis (Fin n) R M)
    (f : GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H) :
    let := b.comoduleOfCoordinateBialgHom f
    Comodule.coefficientMatrix (C := H) b = (GeneralLinear.genericMatrix R n).map f := by
  classical
  let := b.comoduleOfCoordinateBialgHom f
  ext i j
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    comoduleOfCoordinateBialgHom_coact_basis]
  simp [Basis.coord_apply, Finsupp.single_apply]

/-- Recovering the comodule of a coordinate map and then taking its coordinate map returns
the original map. -/
@[simp]
theorem coordinateBialgHom_comoduleOfCoordinateBialgHom (b : Basis (Fin n) R M)
    (f : GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H) :
    let := b.comoduleOfCoordinateBialgHom f
    Comodule.coordinateBialgHom (H := H) b = f := by
  let := b.comoduleOfCoordinateBialgHom f
  apply BialgHom.coe_toAlgHom_injective
  apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
  intro i j
  erw [Comodule.coordinateBialgHom_X]
  rw [coefficientMatrix_comoduleOfCoordinateBialgHom,
    Matrix.map_apply, GeneralLinear.genericMatrix_apply]
  rfl

/-- The comodule recovered from a comodule's coordinate map is the original comodule. -/
@[simp]
theorem comoduleOfCoordinateBialgHom_coordinateBialgHom (b : Basis (Fin n) R M)
    [rho : Comodule R H M] :
    b.comoduleOfCoordinateBialgHom (Comodule.coordinateBialgHom (H := H) b) = rho := by
  apply Comodule.ext
  apply b.ext
  intro j
  rw [comoduleOfCoordinateBialgHom_coact_basis,
    Comodule.coact_basis_eq_sum_coefficientMatrix]
  congr 1
  funext i
  rw [GeneralLinear.genericMatrix_apply, Comodule.coordinateBialgHom_X]

/-- Comodule structures on a finite free module correspond to coordinate representation maps.
The chosen basis specifies the identification of its linear group with `GLₙ`. -/
noncomputable def comoduleEquivCoordinateBialgHom (b : Basis (Fin n) R M) :
    Comodule R H M ≃ (GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H) where
  toFun rho := letI := rho; Comodule.coordinateBialgHom (H := H) b
  invFun := b.comoduleOfCoordinateBialgHom
  left_inv rho := @comoduleOfCoordinateBialgHom_coordinateBialgHom R H M n _ _ _ _ _ b rho
  right_inv := b.coordinateBialgHom_comoduleOfCoordinateBialgHom

/-- The coordinate correspondence sends a comodule to its usual coordinate map. -/
@[simp]
theorem comoduleEquivCoordinateBialgHom_apply (b : Basis (Fin n) R M)
    (rho : Comodule R H M) :
    b.comoduleEquivCoordinateBialgHom rho =
      let := rho
      Comodule.coordinateBialgHom (H := H) b := (rfl)

/-- The inverse coordinate correspondence corestricts the standard representation and
transports it through the chosen basis. -/
@[simp]
theorem comoduleEquivCoordinateBialgHom_symm_apply (b : Basis (Fin n) R M)
    (f : GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H) :
    b.comoduleEquivCoordinateBialgHom.symm f = b.comoduleOfCoordinateBialgHom f := (rfl)

end Module.Basis
