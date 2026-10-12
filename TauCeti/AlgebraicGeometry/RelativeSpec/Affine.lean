/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor

/-!
# Relative Spec over an affine scheme

For a quasi-coherent commutative algebra `A` on an affine scheme `X`, the relative spectrum
is canonically `Spec Γ(A.X, ⊤)`. The inverse of this identification is the chart inclusion
over the whole base. It respects the structure morphism to `X` and is natural in algebra
morphisms, identifying relative Spec on an affine base with the usual contravariant spectrum
of the algebra of global sections.

The construction uses `CommMon.isPullback_relativeSpecCover`: the chart over the whole base
is an isomorphism because it is the pullback of the isomorphism `X.topIso.hom`.

## References

* The Stacks Project, Tag 01LL, Lemma 27.3.4 (relative spectrum via gluing).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X : Scheme.{u}} [IsAffine X]
variable (A : CommMon X.Modules) [A.X.IsQuasicoherent]

/-- Over an affine base, the chart of relative Spec over the whole base is an isomorphism. -/
instance isIso_relativeSpecCover_f_top :
    IsIso (A.relativeSpecCover.f ⟨⊤, isAffineOpen_top X⟩) := by
  have : IsIso (Scheme.Opens.ι (⊤ : X.Opens)) :=
    inferInstanceAs (IsIso X.topIso.hom)
  exact (A.isPullback_relativeSpecCover ⟨⊤, isAffineOpen_top X⟩).isIso_snd_of_isIso

/-- Relative Spec over an affine scheme is the spectrum of the algebra of global sections.
The inverse is the chart inclusion over the whole base. -/
def relativeSpecIsoSpec : A.relativeSpec ≅ Spec (CommRingCat.of Γ(A.X, ⊤)) :=
  (asIso (A.relativeSpecCover.f ⟨⊤, isAffineOpen_top X⟩)).symm

/-- The inverse affine normalization is the chart inclusion over the whole base. -/
@[simp]
lemma relativeSpecIsoSpec_inv :
    A.relativeSpecIsoSpec.inv = A.relativeSpecCover.f ⟨⊤, isAffineOpen_top X⟩ :=
  (rfl)

/-- Affine normalization identifies the map to the base with Spec of the structure map
on global sections, followed by the affine identification of the base. -/
@[reassoc]
lemma relativeSpecIsoSpec_inv_relativeSpecToBase :
    A.relativeSpecIsoSpec.inv ≫ A.relativeSpecToBase =
      Spec.map (A.toSectionsPresheaf.app (op ⊤)) ≫ X.isoSpec.inv := by
  exact (A.relativeSpecCover_f_relativeSpecToBase ⟨⊤, isAffineOpen_top X⟩).trans
    (congrArg (Spec.map (A.toSectionsPresheaf.app (op ⊤)) ≫ ·)
      (IsAffineOpen.fromSpec_top (X := X)))

/-- The affine coordinate description of the structure morphism of relative Spec. -/
@[reassoc (attr := simp)]
lemma relativeSpecIsoSpec_hom_toBase :
    A.relativeSpecIsoSpec.hom ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) Γ(A.X, ⊤))) ≫ X.isoSpec.inv) =
      A.relativeSpecToBase := by
  have h := A.relativeSpecIsoSpec_inv_relativeSpecToBase
  rw [toSectionsPresheaf_app] at h
  exact (A.relativeSpecIsoSpec.inv_comp_eq.mp h).symm

variable {A} {B : CommMon X.Modules} [B.X.IsQuasicoherent]

/-- Affine normalization is contravariantly natural in the quasi-coherent algebra. -/
@[reassoc (attr := simp)]
lemma relativeSpecIsoSpec_hom_naturality (f : A ⟶ B) :
    relativeSpecMap f ≫ A.relativeSpecIsoSpec.hom =
      B.relativeSpecIsoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (sectionsAlgHom f ⊤).toRingHom) := by
  have h : B.relativeSpecIsoSpec.inv ≫ relativeSpecMap f =
      Spec.map (CommRingCat.ofHom (sectionsAlgHom f ⊤).toRingHom) ≫
        A.relativeSpecIsoSpec.inv :=
    relativeSpecCover_f_relativeSpecMap f ⟨⊤, isAffineOpen_top X⟩
  apply (B.relativeSpecIsoSpec.inv_comp_eq).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (· ≫ A.relativeSpecIsoSpec.hom) h

end

end CategoryTheory.CommMon

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u}) [IsAffine X]

/-- On an affine base, take the spectrum of the global sections of a quasi-coherent algebra,
with its structure map to the base induced by the algebra map on global sections. -/
@[expose]
def specGlobalSections : (QuasicoherentAlgebra X)ᵒᵖ ⥤ AffineSchemeOver X where
  obj A := MorphismProperty.Over.mk ⊤
    (Spec.map (A.unop.obj.toSectionsPresheaf.app (op ⊤)) ≫ X.isoSpec.inv) inferInstance
  map {A B} f := MorphismProperty.Over.homMk
    (Spec.map ((CommMon.sectionsPresheafMap f.unop.hom).app (op ⊤))) (by
      have h := NatTrans.congr_app
        (CommMon.toSectionsPresheaf_comp_sectionsPresheafMap f.unop.hom) (op ⊤)
      rw [NatTrans.comp_app] at h
      exact (Spec.map_comp_assoc _ _ X.isoSpec.inv).symm.trans
        (congrArg (fun h ↦ Spec.map h ≫ X.isoSpec.inv) h))
  map_id A := by
    apply MorphismProperty.Over.Hom.ext
    exact (congrArg Spec.map (NatTrans.congr_app
      (CommMon.sectionsPresheafMap_id A.unop.obj) (op ⊤))).trans (Spec.map_id _)
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (congrArg Spec.map (NatTrans.congr_app
      (CommMon.sectionsPresheafMap_comp g.unop.hom f.unop.hom) (op ⊤))).trans
        (Spec.map_comp _ _)

/-- The scheme obtained by the global-sections construction is the ordinary spectrum
of the ring of global sections of the algebra. -/
@[simp]
lemma specGlobalSections_obj_left (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((specGlobalSections X).obj A).left = Spec (CommRingCat.of Γ(A.unop.obj.X, ⊤)) :=
  (rfl)

/-- The structure morphism of the global-sections construction is induced by the algebra map. -/
@[simp]
lemma specGlobalSections_obj_hom (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((specGlobalSections X).obj A).hom =
      Spec.map (A.unop.obj.toSectionsPresheaf.app (op ⊤)) ≫ X.isoSpec.inv :=
  (rfl)

/-- On morphisms, the global-sections construction is Spec of the algebra homomorphism
on global sections. -/
@[simp]
lemma specGlobalSections_map_left {A B : (QuasicoherentAlgebra X)ᵒᵖ} (f : A ⟶ B) :
    ((specGlobalSections X).map f).left =
      Spec.map (CommRingCat.ofHom (CommMon.sectionsAlgHom f.unop.hom ⊤).toRingHom) := by
  exact congrArg Spec.map (CommMon.sectionsPresheafMap_app f.unop.hom (op ⊤))

/-- On an affine base, relative Spec is naturally the usual spectrum of global sections,
as a functor to affine schemes over the base. -/
def relativeSpecAffineIso : relativeSpec X ≅ specGlobalSections X :=
  NatIso.ofComponents
    (fun A ↦ MorphismProperty.Over.isoMk A.unop.obj.relativeSpecIsoSpec
      (by
        rw [specGlobalSections_obj_hom, CommMon.toSectionsPresheaf_app]
        exact A.unop.obj.relativeSpecIsoSpec_hom_toBase))
    (fun {A B} f ↦ by
      apply MorphismProperty.Over.Hom.ext
      -- The affine over-category is a specialization of the morphism-property comma
      -- category; rewriting its composition lemma does not see through that specialization.
      change CommMon.relativeSpecMap f.unop.hom ≫ B.unop.obj.relativeSpecIsoSpec.hom =
        A.unop.obj.relativeSpecIsoSpec.hom ≫ ((specGlobalSections X).map f).left
      rw [specGlobalSections_map_left]
      exact CommMon.relativeSpecIsoSpec_hom_naturality f.unop.hom)

/-- The components of affine normalization use the canonical chart isomorphisms. -/
@[simp]
lemma relativeSpecAffineIso_hom_app_left (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpecAffineIso X).hom.app A).left = A.unop.obj.relativeSpecIsoSpec.hom :=
  (rfl)

/-- The inverse component of affine normalization is the chart over the whole affine base. -/
@[simp]
lemma relativeSpecAffineIso_inv_app_left (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpecAffineIso X).inv.app A).left =
      A.unop.obj.relativeSpecCover.f ⟨⊤, isAffineOpen_top X⟩ := by
  exact A.unop.obj.relativeSpecIsoSpec_inv

end

end TauCeti.AlgebraicGeometry
