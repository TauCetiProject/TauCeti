/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor

/-!
# The relative spectrum of a presheaf of subalgebras of sections

Let `A` be a commutative `𝒪ₓ`-algebra on a scheme `X`. A `CommMon.SubalgebraPresheaf A` is a
family of `Γ(X, U)`-subalgebras `S.sections U` of the sections `Γ(A.X, U)`, stable under
restriction. Such a family is a presheaf of rings `S.sectionsPresheaf` on `X`, under the structure
presheaf and inside the sections of `A`. When it is coequifibered over the structure presheaf on
the affine opens (`CommMon.SubalgebraPresheaf.IsCoequifibered`), that is, when its sections over a
basic open of an affine open are localizations, the affine schemes `Spec (S.sections U)` glue, with
Mathlib's relative gluing on the small affine Zariski site, to a scheme `S.relativeSpec` affine over
`X`. For quasi-coherent `A`, the inclusions of the subalgebras glue to a morphism
`S.relativeSpecπ : A.relativeSpec ⟶ S.relativeSpec` over `X`, which over every affine open of `X`
is `Spec` of the inclusion.

This is the common construction behind the relative spectrum of an equalizer of quasi-coherent
algebras (`CommMon.equalizerSubalgebraPresheaf`) and the quotient of a scheme affine over `X` by a
finite group (`CommMon.invariantSubalgebraPresheaf`).

## Main declarations

* `CommMon.SubalgebraPresheaf A`: families of subalgebras of the sections of `A` stable under
  restriction, with the presheaf of rings `S.sectionsPresheaf`, its structure map
  `S.toSectionsPresheaf` and its inclusion `S.sectionsPresheafι` into the sections of `A`;
* `CommMon.SubalgebraPresheaf.IsCoequifibered`: the localization condition under which the spectra
  glue, with the criterion `CommMon.SubalgebraPresheaf.IsCoequifibered.of_isLocalizationAway`;
* `CommMon.SubalgebraPresheaf.relativeSpec`, with the affine structure morphism
  `CommMon.SubalgebraPresheaf.relativeSpecToBase` and the chart description
  `CommMon.SubalgebraPresheaf.isPullback_relativeSpecCover`;
* `CommMon.SubalgebraPresheaf.relativeSpecπ`, with
  `CommMon.SubalgebraPresheaf.isPullback_relativeSpecπ` and
  `CommMon.SubalgebraPresheaf.relativeSpecMap_relativeSpecπ`.

## References

* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) (relative
  spectrum via gluing).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- A family of `Γ(X, U)`-subalgebras of the sections of a commutative `𝒪ₓ`-algebra `A` over the
opens `U` of `X`, stable under restriction: a sub-presheaf of rings of the sections of `A` under
the structure presheaf. -/
structure SubalgebraPresheaf (A : CommMon X.Modules) where
  /-- The subalgebra of sections over `U`. -/
  sections (U : X.Opens) : Subalgebra Γ(X, U) Γ(A.X, U)
  /-- Restriction of sections preserves the subalgebras. -/
  restrictSections_mem {U V : X.Opens} (i : V ⟶ U) {x : Γ(A.X, U)} :
    x ∈ sections U → A.restrictSections i x ∈ sections V

namespace SubalgebraPresheaf

variable {A : CommMon X.Modules} (S : A.SubalgebraPresheaf)

/-- Two presheaves of subalgebras are equal when they have the same sections over every open. -/
@[ext]
lemma ext {S T : A.SubalgebraPresheaf}
    (h : ∀ (U : X.Opens) (x : Γ(A.X, U)), x ∈ S.sections U ↔ x ∈ T.sections U) : S = T := by
  obtain ⟨S, _⟩ := S
  obtain ⟨T, _⟩ := T
  congr
  exact funext fun U ↦ Subalgebra.ext (h U)

/-- The presheaf of rings `U ↦ S.sections U`. -/
@[expose]
def sectionsPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (S.sections U.unop)
  map i := CommRingCat.ofHom ((A.restrictSections i.unop).restrict _ _
    fun _ ↦ S.restrictSections_mem i.unop)
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom (A.sectionsPresheaf.map_id U) x.1
  map_comp i j := by
    ext x
    exact ConcreteCategory.congr_hom (A.sectionsPresheaf.map_comp i j) x.1

@[simp]
lemma sectionsPresheaf_obj (U : X.Opensᵒᵖ) :
    S.sectionsPresheaf.obj U = CommRingCat.of (S.sections U.unop) :=
  (rfl)

@[simp]
lemma sectionsPresheaf_map {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    S.sectionsPresheaf.map i =
      CommRingCat.ofHom ((A.restrictSections i.unop).restrict _ _
        fun _ ↦ S.restrictSections_mem i.unop) :=
  (rfl)

/-- The structure morphism from the structure presheaf of `X`: regular functions act on `A`
through the algebra map, whose image lies in every subalgebra. -/
def toSectionsPresheaf : X.presheaf ⟶ S.sectionsPresheaf where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) (S.sections U.unop))
  naturality {U V} i := by
    ext r
    exact Subtype.ext (A.restrictSections_algebraMap i.unop r).symm

@[simp]
lemma toSectionsPresheaf_app (U : X.Opensᵒᵖ) :
    S.toSectionsPresheaf.app U =
      CommRingCat.ofHom (algebraMap Γ(X, U.unop) (S.sections U.unop)) :=
  (rfl)

/-- The inclusion of the subalgebras into all sections of `A`. -/
def sectionsPresheafι : S.sectionsPresheaf ⟶ A.sectionsPresheaf where
  app U := CommRingCat.ofHom (S.sections U.unop).val.toRingHom
  naturality _ _ _ := (rfl)

@[simp]
lemma sectionsPresheafι_app (U : X.Opensᵒᵖ) :
    S.sectionsPresheafι.app U = CommRingCat.ofHom (S.sections U.unop).val.toRingHom :=
  (rfl)

/-- The inclusion of the subalgebras is the algebra map of the subalgebra. -/
lemma sectionsPresheafι_app_eq_algebraMap (U : X.Opens) :
    S.sectionsPresheafι.app (op U) =
      CommRingCat.ofHom (algebraMap (S.sections U) Γ(A.X, U)) :=
  (rfl)

/-- The inclusion of the subalgebras is compatible with the structure maps from the structure
presheaf. -/
@[reassoc (attr := simp)]
lemma toSectionsPresheaf_comp_sectionsPresheafι :
    S.toSectionsPresheaf ≫ S.sectionsPresheafι = A.toSectionsPresheaf := by
  ext U r
  rw [NatTrans.comp_app, CommMon.toSectionsPresheaf_app]
  rfl

/-- If the algebra morphisms `f` and `g` agree on the subalgebras, the inclusion of the
subalgebras equalizes the morphisms of section rings they induce. -/
lemma sectionsPresheafι_comp_sectionsPresheafMap {B : CommMon X.Modules} {f g : A ⟶ B}
    (h : ∀ (U : X.Opens) (x : Γ(A.X, U)), x ∈ S.sections U →
      sectionsAlgHom f U x = sectionsAlgHom g U x) :
    S.sectionsPresheafι ≫ sectionsPresheafMap f = S.sectionsPresheafι ≫ sectionsPresheafMap g := by
  ext U x
  simp only [NatTrans.comp_app, sectionsPresheafMap_app, sectionsPresheafι_app]
  exact h _ _ x.2

/-- On the affine opens of `X`, the presheaf of rings `S.sectionsPresheaf` is coequifibered over
the structure presheaf: its sections over basic opens are localizations. This is the condition
under which Mathlib glues the spectra of its sections
(`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData`). -/
class IsCoequifibered : Prop where
  /-- The structure map of `S`, restricted to the affine opens, is coequifibered. -/
  coequifibered_toSectionsPresheaf :
    ((toOpensFunctor X).op.whiskerLeft S.toSectionsPresheaf).Coequifibered

variable {S} in
/-- `S` is coequifibered when, over the basic open `X.basicOpen r` of every affine open `U`, its
subalgebra is the localization away from `r` of its subalgebra over `U`. -/
lemma IsCoequifibered.of_isLocalizationAway
    (h : ∀ {U : X.Opens} (_ : IsAffineOpen U) (r : Γ(X, U)),
      letI := ((A.restrictSections (homOfLE (X.basicOpen_le r))).restrict (S.sections U)
        (S.sections (X.basicOpen r)) fun _ ↦ S.restrictSections_mem _).toAlgebra
      IsLocalization.Away (algebraMap Γ(X, U) (S.sections U) r) (S.sections (X.basicOpen r))) :
    S.IsCoequifibered :=
  ⟨coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ h U.2 r⟩

variable [S.IsCoequifibered]

/-- The relative gluing datum of `S`: the affine schemes `Spec (S.sections U)` over the affine
opens `U` of `X`. -/
@[expose]
def relativeSpecGluingData : (directedCover X).RelativeGluingData :=
  relativeGluingData (IsCoequifibered.coequifibered_toSectionsPresheaf (S := S))

/-- The gluing diagram of the relative spectrum of `S` is locally directed. -/
instance isLocallyDirected_relativeSpecGluingData :
    (S.relativeSpecGluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  isLocallyDirected_relativeGluingData _

/-- The relative spectrum of a coequifibered presheaf of subalgebras of the sections of `A`, glued
from the affine schemes `Spec (S.sections U)` over the affine opens `U` of `X`. -/
@[expose]
def relativeSpec : Scheme.{u} :=
  S.relativeSpecGluingData.glued

/-- The structure morphism of the relative spectrum of `S`. -/
@[expose]
def relativeSpecToBase : S.relativeSpec ⟶ X :=
  S.relativeSpecGluingData.toBase

/-- The open cover of the relative spectrum of `S` by the spectra of its subalgebras over the
affine opens of `X`. -/
@[expose]
def relativeSpecCover : S.relativeSpec.OpenCover :=
  S.relativeSpecGluingData.cover

instance isOpenImmersion_relativeSpecCover_f (U : X.AffineZariskiSite) :
    IsOpenImmersion (S.relativeSpecCover.f U) :=
  isOpenImmersion_relativeGluingData_cover_f _ U

lemma relativeSpecCover_X (U : X.AffineZariskiSite) :
    S.relativeSpecCover.X U = Spec (CommRingCat.of (S.sections U.1)) :=
  relativeGluingData_cover_X _ U

/-- Over an affine open `U`, the structure morphism of the relative spectrum of `S` is `Spec` of
the structure map `Γ(X, U) ⟶ S.sections U`. -/
@[reassoc (attr := simp)]
lemma relativeSpecCover_f_relativeSpecToBase (U : X.AffineZariskiSite) :
    S.relativeSpecCover.f U ≫ S.relativeSpecToBase =
      Spec.map (S.toSectionsPresheaf.app (op U.1)) ≫ U.2.fromSpec :=
  relativeGluingData_cover_f_toBase (IsCoequifibered.coequifibered_toSectionsPresheaf (S := S)) U

/-- The preimage of an affine open `U` under the structure morphism of the relative spectrum of
`S` is the image of its chart over `U`. -/
lemma relativeSpecToBase_preimage (U : X.AffineZariskiSite) :
    S.relativeSpecToBase ⁻¹ᵁ U.1 = (S.relativeSpecCover.f U).opensRange :=
  relativeGluingData_toBase_preimage (IsCoequifibered.coequifibered_toSectionsPresheaf (S := S)) U

/-- Over an affine open `U` of `X`, the relative spectrum of `S` is `Spec (S.sections U)`. -/
lemma isPullback_relativeSpecCover (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (S.toSectionsPresheaf.app (op U.1)) ≫ U.2.isoSpec.inv)
      (S.relativeSpecCover.f U) U.1.ι S.relativeSpecToBase :=
  isPullback_relativeGluingData_cover (IsCoequifibered.coequifibered_toSectionsPresheaf (S := S)) U

/-- The structure morphism of the relative spectrum of `S` is affine. -/
instance isAffineHom_relativeSpecToBase : IsAffineHom S.relativeSpecToBase :=
  isAffineHom_relativeGluingData_toBase (IsCoequifibered.coequifibered_toSectionsPresheaf (S := S))

/-- Maps out of the relative spectrum of `S` are determined on its affine charts. -/
lemma relativeSpec_hom_ext {T : Scheme.{u}} {f g : S.relativeSpec ⟶ T}
    (h : ∀ U : X.AffineZariskiSite, S.relativeSpecCover.f U ≫ f = S.relativeSpecCover.f U ≫ g) :
    f = g :=
  colimit.hom_ext h

variable [A.X.IsQuasicoherent]

/-- The morphism `Spec_X(A) ⟶ S.relativeSpec` over `X`, given on each affine chart by `Spec` of
the inclusion `S.sections U ⟶ Γ(A.X, U)`. -/
def relativeSpecπ : A.relativeSpec ⟶ S.relativeSpec :=
  colimMap (Functor.whiskerRight
    (((toOpensFunctor X).op.whiskerLeft S.sectionsPresheafι).rightOp) Scheme.Spec)

/-- On an affine chart, `S.relativeSpecπ` is `Spec` of the inclusion of the subalgebra. -/
@[reassoc (attr := simp)]
lemma relativeSpecCover_f_relativeSpecπ (U : X.AffineZariskiSite) :
    A.relativeSpecCover.f U ≫ S.relativeSpecπ =
      Spec.map (S.sectionsPresheafι.app (op U.1)) ≫ S.relativeSpecCover.f U :=
  ι_colimMap _ U

/-- `S.relativeSpecπ` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma relativeSpecπ_relativeSpecToBase :
    S.relativeSpecπ ≫ S.relativeSpecToBase = A.relativeSpecToBase := by
  apply A.relativeSpec_hom_ext
  intro U
  -- Rebind the chart inclusions and the ring maps at their explicit sources and targets,
  -- rather than the definitionally equal objects of the open covers and of the presheaves, so
  -- that ordinary rewriting applies.
  let ιA : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιS : Spec (CommRingCat.of (S.sections U.1)) ⟶ S.relativeSpec := S.relativeSpecCover.f U
  let iU : CommRingCat.of (S.sections U.1) ⟶ CommRingCat.of Γ(A.X, U.1) :=
    S.sectionsPresheafι.app (op U.1)
  let eU : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of (S.sections U.1) :=
    S.toSectionsPresheaf.app (op U.1)
  let aU : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of Γ(A.X, U.1) :=
    A.toSectionsPresheaf.app (op U.1)
  have hπ : ιA ≫ S.relativeSpecπ = Spec.map iU ≫ ιS := S.relativeSpecCover_f_relativeSpecπ U
  have hS : ιS ≫ S.relativeSpecToBase = Spec.map eU ≫ U.2.fromSpec :=
    S.relativeSpecCover_f_relativeSpecToBase U
  have hA : ιA ≫ A.relativeSpecToBase = Spec.map aU ≫ U.2.fromSpec :=
    A.relativeSpecCover_f_relativeSpecToBase U
  have hcomp : eU ≫ iU = aU :=
    NatTrans.congr_app S.toSectionsPresheaf_comp_sectionsPresheafι (op U.1)
  change ιA ≫ S.relativeSpecπ ≫ S.relativeSpecToBase = ιA ≫ A.relativeSpecToBase
  rw [reassoc_of% hπ, hS, ← Spec.map_comp_assoc, hcomp, hA]

/-- If the algebra morphisms `f` and `g` agree on the subalgebras, then `S.relativeSpecπ`
coequalizes the morphisms of relative spectra they induce. -/
lemma relativeSpecMap_relativeSpecπ {B : CommMon X.Modules} [B.X.IsQuasicoherent] {f g : A ⟶ B}
    (h : ∀ (U : X.Opens) (x : Γ(A.X, U)), x ∈ S.sections U →
      sectionsAlgHom f U x = sectionsAlgHom g U x) :
    relativeSpecMap f ≫ S.relativeSpecπ = relativeSpecMap g ≫ S.relativeSpecπ := by
  apply B.relativeSpec_hom_ext
  intro U
  -- Rebind the chart inclusions and the ring maps at their explicit sources, as above.
  let ιA : Spec (CommRingCat.of Γ(A.X, U.1)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιB : Spec (CommRingCat.of Γ(B.X, U.1)) ⟶ B.relativeSpec := B.relativeSpecCover.f U
  let ιS : Spec (CommRingCat.of (S.sections U.1)) ⟶ S.relativeSpec := S.relativeSpecCover.f U
  let iU : CommRingCat.of (S.sections U.1) ⟶ CommRingCat.of Γ(A.X, U.1) :=
    S.sectionsPresheafι.app (op U.1)
  let hU (k : A ⟶ B) : CommRingCat.of Γ(A.X, U.1) ⟶ CommRingCat.of Γ(B.X, U.1) :=
    CommRingCat.ofHom (sectionsAlgHom k U.1).toRingHom
  have hπ : ιA ≫ S.relativeSpecπ = Spec.map iU ≫ ιS := S.relativeSpecCover_f_relativeSpecπ U
  have hB (k : A ⟶ B) : ιB ≫ relativeSpecMap k = Spec.map (hU k) ≫ ιA :=
    relativeSpecCover_f_relativeSpecMap k U
  -- On the chart over `U`, both composites are `Spec` of the inclusion of the subalgebra
  -- followed by the algebra map on sections.
  have key (k : A ⟶ B) : ιB ≫ relativeSpecMap k ≫ S.relativeSpecπ =
      Spec.map (iU ≫ hU k) ≫ ιS := by
    rw [reassoc_of% hB k, hπ, ← Spec.map_comp_assoc]
  have hι : iU ≫ hU f = iU ≫ hU g := by
    have h := NatTrans.congr_app (S.sectionsPresheafι_comp_sectionsPresheafMap h) (op U.1)
    rwa [NatTrans.comp_app, NatTrans.comp_app, sectionsPresheafMap_app,
      sectionsPresheafMap_app] at h
  change ιB ≫ relativeSpecMap f ≫ S.relativeSpecπ = ιB ≫ relativeSpecMap g ≫ S.relativeSpecπ
  rw [key f, key g, hι]

/-- Over an affine open `U` of `X`, `S.relativeSpecπ` is `Spec` of the inclusion
`S.sections U ⟶ Γ(A.X, U)`: the square formed with the two charts over `U` is a pullback
square. -/
lemma isPullback_relativeSpecπ (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (S.sectionsPresheafι.app (op U.1))) (A.relativeSpecCover.f U)
      (S.relativeSpecCover.f U) S.relativeSpecπ := by
  refine IsPullback.of_right ?_ (S.relativeSpecCover_f_relativeSpecπ U).symm
    (S.isPullback_relativeSpecCover U)
  rw [relativeSpecπ_relativeSpecToBase, ← Spec.map_comp_assoc, ← NatTrans.comp_app,
    toSectionsPresheaf_comp_sectionsPresheafι]
  exact A.isPullback_relativeSpecCover U

/-- A morphism property which is local on the target holds for `S.relativeSpecπ` exactly when it
holds for `Spec` of the inclusions `S.sections U ⟶ Γ(A.X, U)` over the affine opens `U` of
`X`. -/
lemma relativeSpecπ_iff (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] :
    P S.relativeSpecπ ↔ ∀ U : X.AffineZariskiSite,
      P (Spec.map (CommRingCat.ofHom (algebraMap (S.sections U.1) Γ(A.X, U.1)))) := by
  simp only [← sectionsPresheafι_app_eq_algebraMap]
  refine ⟨fun H U ↦ MorphismProperty.IsLocalAtTarget.of_isPullback S.relativeSpecCover U
    (S.isPullback_relativeSpecπ U).flip H,
    fun H ↦ MorphismProperty.IsLocalAtTarget.of_zeroHypercover S.relativeSpecCover
      fun U ↦ ?_⟩
  -- The second projection of the pullback is the chart of `S.relativeSpecπ`, up to isomorphism.
  have h := (S.isPullback_relativeSpecπ U).flip
  exact h.isoPullback_inv_snd ▸ (P.cancel_left_of_respectsIso h.isoPullback.inv _).mpr (H U)

end SubalgebraPresheaf

end

end CategoryTheory.CommMon
