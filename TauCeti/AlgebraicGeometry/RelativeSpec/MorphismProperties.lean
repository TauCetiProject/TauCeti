/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Morphism properties of relative spectra

The structure morphism `Spec_X(A) ⟶ X` of a quasi-coherent algebra has finite type, finite
presentation, finiteness, integrality, or the closed-immersion property exactly when its sections
algebra has the corresponding property over each affine open of `X`. These criteria let one
check a geometric property directly on the algebra from which the relative spectrum is built.

The finite-type and finite-presentation criteria use Mathlib's `LocallyOfFiniteType` and
`LocallyOfFinitePresentation`: the structure morphism is already affine, hence quasi-compact
and separated, so these are also the global finite-type and finite-presentation conditions.
The proofs use the existing relative-spectrum chart pullbacks and Mathlib's criteria for
morphisms of affine schemes.

## References

* The Stacks Project, [Tag 01LX](https://stacks.math.columbia.edu/tag/01LX), relative spectrum.
* The Stacks Project, [Tag 01T2](https://stacks.math.columbia.edu/tag/01T2), finite type.
* The Stacks Project, [Tag 01TQ](https://stacks.math.columbia.edu/tag/01TQ), finite presentation.
* The Stacks Project, [Tag 01WI](https://stacks.math.columbia.edu/tag/01WI), finite morphisms.
* The Stacks Project, [Tag 02K8](https://stacks.math.columbia.edu/tag/02K8), integral morphisms.
* The Stacks Project, [Tag 01QO](https://stacks.math.columbia.edu/tag/01QO), closed immersions.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon X.Modules) [A.X.IsQuasicoherent]

private lemma relativeSpecToBase_iff (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] :
    P A.relativeSpecToBase ↔
      ∀ U : X.affineOpens,
        P (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(A.X, U.1)))) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top X)]
  apply forall_congr'
  intro U
  have h := A.isPullback_relativeSpecCover ⟨U.1, U.2⟩
  have h' := isPullback_morphismRestrict A.relativeSpecToBase U.1
  rw [← P.cancel_left_of_respectsIso (h.isoIsPullback _ _ h').hom,
    h.isoIsPullback_hom_fst _ _ h', P.cancel_right_of_respectsIso,
    toSectionsPresheaf_app]
  rfl

/-- The relative spectrum is of finite type over the base exactly when its sections algebra
is of finite type over the structure ring on every affine open. Affineness already supplies
quasi-compactness. -/
lemma relativeSpec_finiteType_iff :
    LocallyOfFiniteType A.relativeSpecToBase ↔
      ∀ (U : X.Opens), IsAffineOpen U → Algebra.FiniteType Γ(X, U) Γ(A.X, U) := by
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FiniteType)
  rw [A.relativeSpecToBase_iff @LocallyOfFiniteType]
  simp_rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType),
    CommRingCat.hom_ofHom, RingHom.finiteType_algebraMap]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The relative spectrum is of finite presentation over the base exactly when its sections
algebra is finitely presented over the structure ring on every affine open. Affineness already
supplies quasi-compactness and quasi-separatedness. -/
lemma relativeSpec_finitePresentation_iff :
    LocallyOfFinitePresentation A.relativeSpecToBase ↔
      ∀ (U : X.Opens), IsAffineOpen U → Algebra.FinitePresentation Γ(X, U) Γ(A.X, U) := by
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FinitePresentation)
  rw [A.relativeSpecToBase_iff @LocallyOfFinitePresentation]
  simp_rw [LocallyOfFinitePresentation.SpecMap_iff,
    CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The relative spectrum is finite over the base exactly when its sections on every affine
open form a finite module over the structure ring. -/
lemma relativeSpec_finite_iff :
    IsFinite A.relativeSpecToBase ↔
      ∀ (U : X.Opens), IsAffineOpen U → Module.Finite Γ(X, U) Γ(A.X, U) := by
  observe hasFiniteAffineProperty : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget @IsFinite.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hasFiniteAffineProperty
  rw [A.relativeSpecToBase_iff @IsFinite]
  simp_rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.finite_algebraMap]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The relative spectrum is integral over the base exactly when its sections algebra
is integral over the structure ring on every affine open. -/
lemma relativeSpec_integral_iff :
    IsIntegralHom A.relativeSpecToBase ↔
      ∀ (U : X.Opens), IsAffineOpen U → Algebra.IsIntegral Γ(X, U) Γ(A.X, U) := by
  have : IsZariskiLocalAtTarget @IsIntegralHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
  rw [A.relativeSpecToBase_iff @IsIntegralHom]
  simp_rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom,
    algebraMap_isIntegral_iff]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The relative spectrum is a closed subscheme of the base exactly when its algebra is a
quotient of the structure ring on every affine open. -/
lemma relativeSpec_isClosedImmersion_iff :
    IsClosedImmersion A.relativeSpecToBase ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        Function.Surjective (algebraMap Γ(X, U) Γ(A.X, U)) := by
  rw [A.relativeSpecToBase_iff @IsClosedImmersion]
  have h (U : X.affineOpens) :=
    IsClosedImmersion.hasAffineProperty.SpecMap_iff_of_affineAnd
      RingHom.surjective_respectsIso
      (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(A.X, U.1)))
  simp_rw [h, CommRingCat.hom_ofHom]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

end

end CategoryTheory.CommMon
