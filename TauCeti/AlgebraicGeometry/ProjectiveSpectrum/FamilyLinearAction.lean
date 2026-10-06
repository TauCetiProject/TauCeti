/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricBaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
public import Mathlib.CategoryTheory.Conj

/-!
# Families of projective linear transformations

A linear automorphism of `S ⊗[R] M` induces an automorphism of
`Proj(Sym_R M) ×_{Spec R} Spec S` fixing the second projection. Thus a matrix with
coefficients in `S` defines a scheme-theoretic family of projective transformations,
including over nonreduced parameter rings. Flatness of `S` is required by the available
projective base-change comparison; over a field it is automatic. No finiteness or
projectivity assumption on `M` is needed.

We use the convention that `M` is the module of homogeneous linear coordinates.
For projective lines in a finite projective module `V`, use `M = V∨` and the
contragredient action. The construction combines `Proj.symmetricAlgebraScalarTensorIso`,
`Proj.baseChangeIso`, `Proj.symmetricAlgebraAut`, and Mathlib's `Iso.conjAut`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective actions and homogeneous spaces.
-/

public section

open CategoryTheory CategoryTheory.Limits
open TauCeti.SymmetricAlgebra
open scoped TensorProduct

namespace AlgebraicGeometry.Proj

universe u

variable (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The scalar-extended symmetric-algebra presentation identifies projective space with
its scheme fiber product after flat extension of coefficients. -/
noncomputable def symmetricAlgebraBaseChangeIso [Module.Flat R S] :
    Proj (homogeneousSubmodule S (S ⊗[R] M)) ≅
      pullback (toSpecCoeff (homogeneousSubmodule R M))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  symmetricAlgebraScalarTensorIso R S M ≪≫ baseChangeIso (homogeneousSubmodule R M) S

/-- The projective projection of the comparison is the scalar-tensor comparison followed
by the projective coefficient projection. -/
@[reassoc (attr := simp)]
theorem symmetricAlgebraBaseChangeIso_hom_fst [Module.Flat R S] :
    (symmetricAlgebraBaseChangeIso R S M).hom ≫ pullback.fst _ _ =
      (symmetricAlgebraScalarTensorIso R S M).hom ≫
        baseChangeProjection (homogeneousSubmodule R M) S := by
  simp [symmetricAlgebraBaseChangeIso]

/-- The parameter projection of the comparison is the coefficient structure morphism. -/
@[reassoc (attr := simp)]
theorem symmetricAlgebraBaseChangeIso_hom_snd [Module.Flat R S] :
    (symmetricAlgebraBaseChangeIso R S M).hom ≫ pullback.snd _ _ =
      toSpecCoeff (homogeneousSubmodule S (S ⊗[R] M)) := by
  simp only [symmetricAlgebraBaseChangeIso, Iso.trans_hom, Category.assoc,
    baseChangeIso_hom_snd, toSpecCoeff_def,
    symmetricAlgebraScalarTensorIso_hom_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp,
    scalarTensorGradedAlgHom_gradedZeroRingHom_comp_algebraMap]

/-- The inverse comparison preserves the parameter projection. -/
@[reassoc (attr := simp)]
theorem symmetricAlgebraBaseChangeIso_inv_toSpecCoeff [Module.Flat R S] :
    (symmetricAlgebraBaseChangeIso R S M).inv ≫
        toSpecCoeff (homogeneousSubmodule S (S ⊗[R] M)) = pullback.snd _ _ := by
  rw [← symmetricAlgebraBaseChangeIso_hom_snd R S M, Iso.inv_hom_id_assoc]

variable [Module.Flat R S]

/-- Linear automorphisms with parameter coefficients give projective scheme automorphisms
of the fiber product. Multiplication is ordinary function composition. -/
noncomputable def symmetricAlgebraFamilyAut :
    ((S ⊗[R] M) ≃ₗ[S] (S ⊗[R] M)) →*
      Aut (pullback (toSpecCoeff (homogeneousSubmodule R M))
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :=
  (symmetricAlgebraBaseChangeIso R S M).conjAut.toMonoidHom.comp
    (symmetricAlgebraAut S)

/-- The family is obtained by transporting inverse projective pullback through the
base-change comparison. -/
theorem symmetricAlgebraFamilyAut_apply (e : (S ⊗[R] M) ≃ₗ[S] (S ⊗[R] M)) :
    symmetricAlgebraFamilyAut R S M e =
      (symmetricAlgebraBaseChangeIso R S M).symm ≪≫
        symmetricAlgebraMapIso S e.symm ≪≫ symmetricAlgebraBaseChangeIso R S M := by
  simp only [symmetricAlgebraFamilyAut, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, symmetricAlgebraAut_apply]
  exact Iso.conjAut_apply _ _

/-- A projective linear family fixes its parameter coordinate as a scheme morphism. -/
@[reassoc (attr := simp)]
theorem symmetricAlgebraFamilyAut_hom_snd (e : (S ⊗[R] M) ≃ₗ[S] (S ⊗[R] M)) :
    (symmetricAlgebraFamilyAut R S M e).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [symmetricAlgebraFamilyAut_apply]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    symmetricAlgebraBaseChangeIso_hom_snd]
  rw [toSpecCoeff_def (homogeneousSubmodule S (S ⊗[R] M)),
    symmetricAlgebraMapIso_hom_toSpecZero_assoc,
    ← toSpecCoeff_def (homogeneousSubmodule S (S ⊗[R] M))]
  exact symmetricAlgebraBaseChangeIso_inv_toSpecCoeff R S M

/-- The inverse family fixes its parameter coordinate as well. -/
@[reassoc (attr := simp)]
theorem symmetricAlgebraFamilyAut_inv_snd (e : (S ⊗[R] M) ≃ₗ[S] (S ⊗[R] M)) :
    (symmetricAlgebraFamilyAut R S M e).inv ≫ pullback.snd _ _ = pullback.snd _ _ := by
  exact (Iso.inv_comp_eq (symmetricAlgebraFamilyAut R S M e)).mpr
    (symmetricAlgebraFamilyAut_hom_snd R S M e).symm

end AlgebraicGeometry.Proj
