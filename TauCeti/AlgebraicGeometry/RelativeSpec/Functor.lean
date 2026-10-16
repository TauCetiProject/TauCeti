/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Functoriality of relative Spec

A morphism of quasi-coherent commutative algebras on a scheme induces a morphism of
relative spectra in the opposite direction. On each affine open, this is the spectrum
of the induced algebra homomorphism on sections. These chart maps determine the global
morphism uniquely and commute with the structure morphisms to the base.

We package this construction as `TauCeti.AlgebraicGeometry.relativeSpec`, from the
opposite category of quasi-coherent algebras to affine schemes over the base. The
functor provides the geometric side of the correspondence between quasi-coherent
commutative algebras and affine schemes over the base, and is an input to the natural
universal property of relative Spec.

## References

* The Stacks Project, Tag 01LL (relative spectrum).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}}

variable {A B C : CommMon X.Modules}
  [A.X.IsQuasicoherent] [B.X.IsQuasicoherent] [C.X.IsQuasicoherent]

/-- The relative spectrum of an algebra morphism, contravariant in the algebra. -/
def _root_.CategoryTheory.CommMon.relativeSpecMap (f : A ⟶ B) :
    B.relativeSpec ⟶ A.relativeSpec :=
  colimMap (Functor.whiskerRight
    (((toOpensFunctor X).op.whiskerLeft (CommMon.sectionsPresheafMap f)).rightOp) Scheme.Spec)

/-- On an affine chart, the relative-spectrum map is Spec of the algebra map on sections. -/
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.CommMon.relativeSpecCover_f_relativeSpecMap
    (f : A ⟶ B) (U : X.AffineZariskiSite) :
    B.relativeSpecCover.f U ≫ CommMon.relativeSpecMap f =
      Spec.map (CommRingCat.ofHom (CommMon.sectionsAlgHom f U.1).toRingHom) ≫
        A.relativeSpecCover.f U := by
  let α : B.relativeSpecGluingData.functor ⟶ A.relativeSpecGluingData.functor :=
    Functor.whiskerRight
      (((toOpensFunctor X).op.whiskerLeft (CommMon.sectionsPresheafMap f)).rightOp) Scheme.Spec
  have hα : α.app U =
      Spec.map (CommRingCat.ofHom (CommMon.sectionsAlgHom f U.1).toRingHom) := by
    dsimp only [α, Functor.whiskerRight_app, NatTrans.rightOp_app, Functor.whiskerLeft_app]
    rw [CommMon.sectionsPresheafMap_app]
    rfl
  exact (ι_colimMap α U).trans (congrArg (· ≫ A.relativeSpecCover.f U) hα)

/-- Maps out of a relative spectrum are determined on its affine charts. -/
@[ext]
lemma _root_.CategoryTheory.CommMon.relativeSpec_hom_ext (A : CommMon X.Modules)
    [A.X.IsQuasicoherent] {T : Scheme.{u}} (f g : A.relativeSpec ⟶ T)
    (h : ∀ U : X.AffineZariskiSite,
      A.relativeSpecCover.f U ≫ f = A.relativeSpecCover.f U ≫ g) : f = g :=
  colimit.hom_ext h

/-- The relative-spectrum map commutes with the structure morphism to the base. -/
@[reassoc (attr := simp)]
lemma _root_.CategoryTheory.CommMon.relativeSpecMap_relativeSpecToBase (f : A ⟶ B) :
    CommMon.relativeSpecMap f ≫ A.relativeSpecToBase = B.relativeSpecToBase := by
  apply B.relativeSpec_hom_ext
  intro U
  let fU := CommRingCat.ofHom (CommMon.sectionsAlgHom f U.1).toRingHom
  -- Rebind chart inclusions at their explicit spectrum source, rather than the
  -- definitionally equal object of the open cover.
  let ιA : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιB : Spec (CommRingCat.of Γ(B.X, U.1)) ⟶ B.relativeSpec := B.relativeSpecCover.f U
  let aU : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of Γ(A.X, U.1) :=
    A.toSectionsPresheaf.app (op U.1)
  let bU : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of Γ(B.X, U.1) :=
    B.toSectionsPresheaf.app (op U.1)
  let pU : Spec (CommRingCat.of Γ(X, U.1)) ⟶ X := U.2.fromSpec
  have hab : aU ≫ fU = bU := by
    have h := NatTrans.congr_app (CommMon.toSectionsPresheaf_comp_sectionsPresheafMap f) (op U.1)
    rw [NatTrans.comp_app, CommMon.sectionsPresheafMap_app] at h
    exact h
  exact calc
    ιB ≫ (CommMon.relativeSpecMap f ≫ A.relativeSpecToBase) =
        (ιB ≫ CommMon.relativeSpecMap f) ≫ A.relativeSpecToBase :=
      (Category.assoc _ _ _).symm
    _ = (Spec.map fU ≫ ιA) ≫ A.relativeSpecToBase :=
      congrArg (· ≫ A.relativeSpecToBase) (CommMon.relativeSpecCover_f_relativeSpecMap f U)
    _ = Spec.map fU ≫ (Spec.map aU ≫ pU) :=
      (Category.assoc _ _ _).trans (congrArg (Spec.map fU ≫ ·)
        (A.relativeSpecCover_f_relativeSpecToBase U))
    _ = Spec.map (aU ≫ fU) ≫ pU :=
      (Spec.map_comp_assoc _ _ _).symm
    _ = Spec.map bU ≫ pU :=
      congrArg (fun h ↦ Spec.map h ≫ pU) hab
    _ = ιB ≫ B.relativeSpecToBase :=
      (B.relativeSpecCover_f_relativeSpecToBase U).symm

@[simp]
lemma _root_.CategoryTheory.CommMon.relativeSpecMap_id (A : CommMon X.Modules)
    [A.X.IsQuasicoherent] : CommMon.relativeSpecMap (𝟙 A) = 𝟙 A.relativeSpec := by
  apply A.relativeSpec_hom_ext
  intro U
  simp only [CommMon.relativeSpecCover_f_relativeSpecMap, Category.comp_id]
  have h : CommRingCat.ofHom (CommMon.sectionsAlgHom (𝟙 A) U.1).toRingHom =
      𝟙 (CommRingCat.of Γ(A.X, U.1)) := by
    rw [CommMon.sectionsAlgHom_id]
    ext x
    simp
  rw [h, Spec.map_id]
  exact Category.id_comp _

@[simp]
lemma _root_.CategoryTheory.CommMon.relativeSpecMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    CommMon.relativeSpecMap (f ≫ g) = CommMon.relativeSpecMap g ≫ CommMon.relativeSpecMap f := by
  apply C.relativeSpec_hom_ext
  intro U
  let fU := CommRingCat.ofHom (CommMon.sectionsAlgHom f U.1).toRingHom
  let gU := CommRingCat.ofHom (CommMon.sectionsAlgHom g U.1).toRingHom
  have hU : CommRingCat.ofHom (CommMon.sectionsAlgHom (f ≫ g) U.1).toRingHom = fU ≫ gU := by
    rw [CommMon.sectionsAlgHom_comp]
    ext x
    simp [fU, gU]
  -- Explicit sources keep the spectrum formulas independent of the cover's
  -- object accessor when composing chart maps.
  let ιA : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιB : Spec (CommRingCat.of Γ(B.X, U.1)) ⟶ B.relativeSpec := B.relativeSpecCover.f U
  let ιC : Spec (CommRingCat.of Γ(C.X, U.1)) ⟶ C.relativeSpec := C.relativeSpecCover.f U
  exact calc
    ιC ≫ CommMon.relativeSpecMap (f ≫ g) =
        Spec.map (fU ≫ gU) ≫ ιA :=
      (CommMon.relativeSpecCover_f_relativeSpecMap (f ≫ g) U).trans
        (congrArg (fun h ↦ Spec.map h ≫ ιA) hU)
    _ = Spec.map gU ≫ (Spec.map fU ≫ ιA) :=
      Spec.map_comp_assoc _ _ _
    _ = Spec.map gU ≫ (ιB ≫ CommMon.relativeSpecMap f) :=
      congrArg (Spec.map gU ≫ ·) (CommMon.relativeSpecCover_f_relativeSpecMap f U).symm
    _ = ιC ≫ (CommMon.relativeSpecMap g ≫ CommMon.relativeSpecMap f) :=
      (CommMon.relativeSpecCover_f_relativeSpecMap_assoc g U _).symm

namespace AlgebraicGeometry

/-- Quasi-coherent commutative algebras on a scheme, with algebra morphisms. -/
abbrev QuasicoherentAlgebra (X : Scheme.{u}) :=
  (show ObjectProperty (CommMon X.Modules) from fun A ↦ A.X.IsQuasicoherent).FullSubcategory

instance (A : QuasicoherentAlgebra X) : A.obj.X.IsQuasicoherent := A.property

/-- Affine schemes over `X`: the structure morphism, not necessarily the scheme, is affine.
Morphisms are arbitrary scheme morphisms over `X`. -/
abbrev AffineSchemeOver (X : Scheme.{u}) :=
  MorphismProperty.Over (@IsAffineHom : MorphismProperty Scheme.{u})
    (⊤ : MorphismProperty Scheme.{u}) X

instance : Category (AffineSchemeOver X) :=
  MorphismProperty.Comma.instCategory _ _ _ _ _

instance (V : AffineSchemeOver X) : IsAffineHom V.hom := V.prop

/-- Relative Spec as a contravariant functor from quasi-coherent commutative algebras to
schemes affine over the base. -/
@[expose]
def relativeSpec (X : Scheme.{u}) : (QuasicoherentAlgebra X)ᵒᵖ ⥤ AffineSchemeOver X where
  obj A := MorphismProperty.Over.mk ⊤ A.unop.obj.relativeSpecToBase inferInstance
  map f := MorphismProperty.Over.homMk (CommMon.relativeSpecMap f.unop.hom)
    (CommMon.relativeSpecMap_relativeSpecToBase f.unop.hom)
  map_id A := by
    apply MorphismProperty.Over.Hom.ext
    exact CommMon.relativeSpecMap_id A.unop.obj
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact CommMon.relativeSpecMap_comp g.unop.hom f.unop.hom

@[simp]
lemma relativeSpec_obj_left (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpec X).obj A).left = A.unop.obj.relativeSpec :=
  (rfl)

@[simp]
lemma relativeSpec_obj_hom (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpec X).obj A).hom = A.unop.obj.relativeSpecToBase :=
  (rfl)

@[simp]
lemma relativeSpec_map_left {A B : (QuasicoherentAlgebra X)ᵒᵖ} (f : A ⟶ B) :
    ((relativeSpec X).map f).left = CommMon.relativeSpecMap f.unop.hom :=
  (rfl)

end AlgebraicGeometry

end

end TauCeti
