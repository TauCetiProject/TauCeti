/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.Norm
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

/-!
# Rational form invariants of an integral lattice

A nondegenerate integral lattice has two determinant invariants: its signed integral Gram
determinant and the square-class discriminant of its ambient rational quadratic form. This file
identifies them. It also records the signed square-class invariant, whose additional factor is
determined solely by the rank.

The comparison lets arithmetic invariants of the rational quadratic space be read directly from
an integral Gram matrix. It is the bridge between the determinant theory of integral lattices and
the regular-form invariants used in local and global classification.

## Main definition

* `TauCeti.IntegralLattice.rationalFormClass`: the regular-form class of the ambient norm form.

## Main results

* `TauCeti.IntegralLattice.discr_rationalFormClass`: the discriminant of the rational form is the
  square class of the lattice determinant.
* `TauCeti.IntegralLattice.signedDiscr_rationalFormClass`: the signed discriminant includes the
  standard rank-dependent sign.
* `TauCeti.IntegralLattice.Isometry.rationalFormClass_eq`: integral-lattice isometries preserve
  the rational form class.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {W : Type w} [AddCommGroup W] [Module ℚ W]

/-- The regular isometry class of the ambient rational norm form of a nondegenerate integral
lattice. -/
noncomputable def rationalFormClass (L : IntegralLattice V) [L.IsNondegenerate] :
    RegularFormClass ℚ :=
  @formClass ℚ _ _ V _ _ L.finiteDimensional L.norm L.nondegenerate_norm

/-- Unfolding the rational form class to the class of the ambient norm quadratic form. -/
theorem rationalFormClass_def (L : IntegralLattice V) [L.IsNondegenerate] :
    L.rationalFormClass =
      @formClass ℚ _ _ V _ _ L.finiteDimensional L.norm L.nondegenerate_norm :=
  (rfl)

/-- The rank of the rational form class is the rank of the lattice carrier. -/
@[simp]
theorem rank_rationalFormClass (L : IntegralLattice V) [L.IsNondegenerate] :
    RegularFormClass.rank L.rationalFormClass = Module.finrank ℤ L := by
  let _ := L.finiteDimensional
  rw [rationalFormClass, rank_formClass, L.finrank_carrier]

/-- The matrix of the ambient norm form in the rationalized carrier basis is the cast of the
integral Gram matrix. -/
theorem toMatrix_norm_rationalBasis (L : IntegralLattice V) :
    L.norm.toMatrix L.rationalBasis =
      (L.gramMatrix (Module.Free.chooseBasis ℤ L)).map (algebraMap ℤ ℚ) := by
  classical
  ext i j
  rw [QuadraticForm.toMatrix, norm_def,
    QuadraticMap.associated_left_inverse' ℚ L.form_flip]
  simp only [LinearMap.toMatrix₂_apply, Matrix.map_apply, rationalBasis_apply]
  rw [algebraMap_int_eq, eq_intCast, intCast_gramMatrix_apply]

/-- The discriminant of the ambient rational form is the square class of the signed integral
Gram determinant. -/
theorem discr_rationalFormClass (L : IntegralLattice V) [L.IsNondegenerate] :
    RegularFormClass.discr L.rationalFormClass = squareClass L.determinantUnit := by
  classical
  let _ := L.finiteDimensional
  apply discr_formClass_eq_squareClass L.norm
    L.nondegenerate_norm L.rationalBasis
  rw [coe_determinantUnit, QuadraticForm.discr, toMatrix_norm_rationalBasis]
  calc
    (L.determinant : ℚ) = (L.gramDet (Module.Free.chooseBasis ℤ L) : ℚ) := by
      exact congrArg (fun z : ℤ ↦ (z : ℚ))
        (L.determinant_eq_gramDet (Module.Free.chooseBasis ℤ L))
    _ = ((L.gramMatrix (Module.Free.chooseBasis ℤ L)).map
        (algebraMap ℤ ℚ)).det := by
      rw [gramDet_def]
      exact (Int.castRingHom ℚ).map_det _

/-- The signed discriminant of the ambient rational form is the determinant square class with
the standard rank-dependent sign correction. -/
theorem signedDiscr_rationalFormClass (L : IntegralLattice V) [L.IsNondegenerate] :
    RegularFormClass.signedDiscr L.rationalFormClass =
      (Module.finrank ℤ L).choose 2 • squareClass (-1 : ℚˣ) +
        squareClass L.determinantUnit := by
  rw [RegularFormClass.signedDiscr_eq_sign_add_discr, rank_rationalFormClass,
    discr_rationalFormClass]

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W}

/-- An integral-lattice isometry preserves the regular class of the ambient rational form. -/
theorem rationalFormClass_eq (e : Isometry L M) [L.IsNondegenerate] [M.IsNondegenerate] :
    L.rationalFormClass = M.rationalFormClass := by
  let _ := L.finiteDimensional
  let _ := M.finiteDimensional
  rw [L.rationalFormClass_def, M.rationalFormClass_def,
    formClass_eq_iff L.norm L.nondegenerate_norm M.norm M.nondegenerate_norm]
  exact ⟨e.normIsometryEquiv⟩

end Isometry

end TauCeti.IntegralLattice
