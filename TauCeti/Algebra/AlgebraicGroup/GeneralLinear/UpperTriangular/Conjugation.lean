/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic

/-!
# Upper-triangular defining ideals after conjugation

If conjugation by a constant invertible matrix makes an algebra-valued point upper triangular,
then that point kills the upper-triangular defining ideal pulled back along the inverse coordinate
automorphism. The criterion applies over any commutative base ring.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.UpperTriangular

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A point whose matrix becomes upper triangular after conjugation by `P` kills the defining
ideal pulled back along the inverse coordinate automorphism. -/
theorem comap_le_ker_of_conjugate
    (P : Matrix.GeneralLinearGroup (Fin n) R) {A : Type v} [CommRing A] [Algebra R A]
    (f : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] A)
    (hf : ((Matrix.GeneralLinearGroup.map (algebraMap R A) P *
        GeneralLinear.pointsMulEquiv n (toConv f) *
        (Matrix.GeneralLinearGroup.map (algebraMap R A) P)⁻¹ :
          Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A).IsUpperTriangular) :
    ((GeneralLinear.UpperTriangular.definingHopfIdeal R n).comapOfSurjective
      (GeneralLinear.conjCoordinateIso P).inv.hom
      (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso P).inv).2).toIdeal ≤
        RingHom.ker f.toRingHom := by
  let c := GeneralLinear.conjCoordinateIso P
  have hmatrix : ((GeneralLinear.pointToGeneralLinear n
      (toConv (f.comp c.hom.hom.toAlgHom)) : Matrix.GeneralLinearGroup (Fin n) A) :
      Matrix (Fin n) (Fin n) A).IsUpperTriangular := by
    rw [← GeneralLinear.pointsMulEquiv_apply]
    rw [GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso]
    exact hf
  have hker := GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
    R n (f.comp c.hom.hom.toAlgHom) hmatrix
  intro x hx
  have hinv : c.inv.hom x ∈ GeneralLinear.UpperTriangular.definingHopfIdeal R n :=
    HopfIdeal.mem_comapOfSurjective.mp hx
  have hzero := hker hinv
  have hc : c.hom.hom (c.inv.hom x) = x := by
    rw [← _root_.CommHopfAlgCat.comp_apply, Iso.inv_hom_id, _root_.CommHopfAlgCat.id_apply]
  rw [RingHom.mem_ker] at hzero ⊢
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hzero ⊢
  simpa only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, hc] using hzero

end TauCeti.GeneralLinear.UpperTriangular
