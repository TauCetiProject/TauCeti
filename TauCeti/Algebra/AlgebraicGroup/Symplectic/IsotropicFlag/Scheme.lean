/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Scheme

/-!
# Scheme-valued points of the symplectic isotropic flag subgroup

The spectrum-points equivalence identifies scheme points with flag-preserving symplectic
matrices. It is natural in the value algebra and compatible with the symplectic inclusion.
The construction uses the canonical transported Hopf spectrum-points API.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic.IsotropicFlag

open GLSymplecticFin.IsotropicFlag

universe u

variable (R : Type u) [CommRing R] (m : ℕ)

section SchemePoints

/-- The flag subgroup's underlying scheme is the spectrum of its coordinate Hopf algebra. -/
theorem groupScheme_X_left :
    (groupScheme R m).X.left =
      AlgebraicGeometry.Spec (CommRingCat.of (coordinateHopfAlgebra R m)) :=
  TauCeti.hopfSpec_obj_X_left R (coordinateHopfAlgebra R m)

variable (A : Type u) [CommRing A] [Algebra R A]

/-- Spectrum identifies algebra points of the flag subgroup with its scheme-valued points. -/
noncomputable def groupSchemePointMulEquiv :
    WithConv (coordinateHopfAlgebra R m →ₐ[R] A) ≃*
      ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation (coordinateHopfAlgebra R m) A rfl

/-- The underlying spectrum map corresponding to an algebra point of the flag subgroup. -/
theorem groupSchemePointMulEquiv_apply_left
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    (groupSchemePointMulEquiv R m A f).left =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
        eqToHom (groupScheme_X_left R m).symm := by
  simpa only [groupSchemePointMulEquiv, AlgHom.toRingHom_eq_coe] using
    CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
      (coordinateHopfAlgebra R m) A (G := groupScheme R m) rfl
        (groupScheme_X_left R m) f

/-- Scheme-valued points of the flag subgroup are the flag-preserving symplectic matrices. -/
noncomputable def schemePointsMulEquiv :
    ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
      (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) ≃*
        matrixSubgroup m (A := A) :=
  (groupSchemePointMulEquiv R m A).symm.trans (pointsMulEquiv R m (A := A))

/-- A scheme point presented by an algebra point gives the same flag-preserving matrix. -/
theorem schemePointsMulEquiv_groupSchemePointMulEquiv
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    schemePointsMulEquiv R m A (groupSchemePointMulEquiv R m A f) =
      pointsMulEquiv R m (A := A) f := by
  simp only [schemePointsMulEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]


/-- Evaluate the flag scheme-points equivalence through its algebra-points presentation. -/
theorem schemePointsMulEquiv_apply
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) :
    schemePointsMulEquiv R m A p =
      pointsMulEquiv R m (A := A) ((groupSchemePointMulEquiv R m A).symm p) := by
  rfl

/-- The inverse sends a flag-preserving matrix to its spectrum-valued point. -/
theorem schemePointsMulEquiv_symm_apply (g : matrixSubgroup m (A := A)) :
    (schemePointsMulEquiv R m A).symm g =
      groupSchemePointMulEquiv R m A ((pointsMulEquiv R m (A := A)).symm g) := by
  rfl

variable {B : Type u} [CommRing B] [Algebra R B]

/-- The flag scheme-points equivalence is covariantly natural in the value algebra. -/
theorem schemePointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) :
    schemePointsMulEquiv R m B
        ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (CommRingCat.of R)) ≫ p) =
      GLSymplecticFin.IsotropicFlag.map m φ.toRingHom (schemePointsMulEquiv R m A p) := by
  unfold schemePointsMulEquiv groupSchemePointMulEquiv
  exact CommHopfAlgCat.mapMulEquivOfPresentation_symm_trans_mapValue
    (coordinateHopfAlgebra R m) φ rfl _ _ _ (pointsMulEquiv_mapValue R m φ) p

private theorem groupSchemePointMulEquiv_comp_inclusion
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    groupSchemePointMulEquiv R m A f ≫ (inclusion R m).hom.hom ≫
        (eqToHom (Symplectic.groupScheme_def R m).symm).hom.hom =
      Symplectic.groupSchemePointMulEquiv m A
        (CommHopfAlgCat.quotientPointsHom (Symplectic.coordinateHopfAlgebra R m)
          (definingHopfIdeal R m) (CommAlgCat.of R A) f) := by
  have h := CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := R) A (G := Symplectic.groupScheme R m) (H' := groupScheme R m)
      (Symplectic.groupScheme_def R m) rfl
      (Symplectic.groupSchemePointMulEquiv m A) (groupSchemePointMulEquiv R m A)
      (Symplectic.groupSchemePointMulEquiv_apply_left m A)
      (fun f => by simpa only [AlgHom.toRingHom_eq_coe] using
        groupSchemePointMulEquiv_apply_left R m A f) (coordinateMap R m) f
  erw [CommHopfAlgCat.mapPointsFunctor_app_apply] at h
  rw [inclusion, CommHopfAlgCat.quotientSpecι_def]
  erw [CommHopfAlgCat.quotientPointsHom_apply]
  simpa only [eqToHom_refl, Category.id_comp, Grp.comp_hom_hom, coordinateMap,
    Category.assoc] using h

/-- Composing with the flag-subgroup inclusion gives the underlying symplectic matrix. -/
theorem schemePointsMulEquiv_comp_inclusion
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) :
    Symplectic.schemePointsMulEquiv m A
        (p ≫ (inclusion R m).hom.hom ≫
          (eqToHom (Symplectic.groupScheme_def R m).symm).hom.hom) =
      (schemePointsMulEquiv R m A p : GLSymplecticFin m A) := by
  obtain ⟨f, rfl⟩ := (groupSchemePointMulEquiv R m A).surjective p
  rw [groupSchemePointMulEquiv_comp_inclusion,
    Symplectic.schemePointsMulEquiv_groupSchemePointMulEquiv,
    schemePointsMulEquiv_groupSchemePointMulEquiv]
  exact pointsMulEquiv_coe R m f

end SchemePoints

end TauCeti.Symplectic.IsotropicFlag
