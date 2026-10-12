/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.AffineFunctions
public import TauCeti.AlgebraicGeometry.RelativeSpec.Affine
public import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Relative Spec recovers its algebra

For a quasi-coherent commutative algebra `A` on a scheme `X`, with structure morphism
`p : Spec_X A ⟶ X`, the algebra of regular functions `p_* 𝒪` of the relative spectrum is
canonically isomorphic to `A`. Above an affine open `U` of `X`, the inverse image of `U` is the
chart `Spec Γ(A.X, U)`, and the comparison is the usual identification of the global functions
on this spectrum with `Γ(A.X, U)`. These comparisons are natural in `U`, so they extend uniquely
from affine opens to an isomorphism of sheaves of rings; it respects the structure maps from
`𝒪ₓ`, hence is an isomorphism of algebras. It is natural in `A`, which gives the algebra-side
unit of the correspondence between quasi-coherent algebras and affine schemes over `X`.

## Main declarations

* `CategoryTheory.CommMon.relativeSpecCoverFunctionAlgebraSectionsRingEquiv`: over an affine
  open, the sections of `p_* 𝒪` are the sections of `A`;
* `CategoryTheory.CommMon.relativeSpecPushforwardIso`: the isomorphism of algebras
  `p_* 𝒪 ≅ A`, and its naturality `relativeSpecPushforwardIso_hom_naturality`;
* `TauCeti.AlgebraicGeometry.relativeSpecUnit`: the natural isomorphism
  `𝟭 ≅ relativeSpec X ⋙ affineFunctions X`.

## References

* The Stacks Project, Tag 01LL (relative spectrum) and Tag 01LQ (relative spectrum as a
  functor).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X : Scheme.{u}} (A : CommMon X.Modules) [A.X.IsQuasicoherent]

/-- The inverse image of an affine open under the structure morphism of the relative spectrum
is the image of its chart. -/
private lemma relativeSpecToBase_preimage_eq_image_top (U : X.AffineZariskiSite) :
    A.relativeSpecToBase ⁻¹ᵁ U.toOpens = A.relativeSpecCover.f U ''ᵁ ⊤ := by
  rw [A.relativeSpecToBase_preimage U, Scheme.Hom.image_top_eq_opensRange]

/-- The chart of the relative spectrum over an affine open `U` lies over `U`. -/
lemma top_le_preimage_relativeSpecToBase (U : X.AffineZariskiSite) :
    ⊤ ≤ A.relativeSpecCover.f U ⁻¹ᵁ (A.relativeSpecToBase ⁻¹ᵁ U.toOpens) := by
  rw [relativeSpecToBase_preimage_eq_image_top A U, Scheme.Hom.preimage_image_eq]

/-- Functions on the inverse image of an affine open `U`, pulled back along the chart
`Spec Γ(A.X, U)` and read as elements of `Γ(A.X, U)`. -/
private def chartSectionsHom (U : X.AffineZariskiSite) :
    Γ(A.relativeSpec, A.relativeSpecToBase ⁻¹ᵁ U.toOpens) ⟶
      A.sectionsPresheaf.obj (op U.toOpens) :=
  (A.relativeSpecCover.f U).appLE _ ⊤ (A.top_le_preimage_relativeSpecToBase U) ≫
    (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, U.toOpens))).hom

private lemma isIso_chartSectionsHom (U : X.AffineZariskiSite) :
    IsIso (chartSectionsHom A U) := by
  let ι := A.relativeSpecCover.f U
  have : IsOpenImmersion ι := A.isOpenImmersion_relativeSpecCover_f U
  have : IsIso (ι.appLE (ι ''ᵁ ⊤) ⊤ (Scheme.Hom.preimage_image_eq _ _).ge) :=
    inferInstanceAs (IsIso (ι.app _ ≫ (A.relativeSpecCover.X U).presheaf.map
      (eqToHom (Scheme.Hom.preimage_image_eq ι ⊤).symm).op))
  have : IsIso (ι.appLE (A.relativeSpecToBase ⁻¹ᵁ U.toOpens) ⊤
      (A.top_le_preimage_relativeSpecToBase U)) := by
    rw [← Scheme.Hom.map_appLE' ι (A.top_le_preimage_relativeSpecToBase U)
      (relativeSpecToBase_preimage_eq_image_top A U).symm]
    infer_instance
  exact IsIso.comp_isIso' this (Iso.isIso_hom _)

/-- The chart comparisons are compatible with restriction between affine opens: the charts are
glued along the spectra of the restriction maps of `A`. -/
private lemma chartSectionsHom_naturality {U U' : X.AffineZariskiSite} (i : U ⟶ U') :
    A.relativeSpec.presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono _ ((toOpensFunctor X).map i).le)).op ≫
      chartSectionsHom A U =
    chartSectionsHom A U' ≫ A.sectionsPresheaf.map ((toOpensFunctor X).map i).op := by
  have hι : Spec.map (A.sectionsPresheaf.map ((toOpensFunctor X).map i).op) ≫
      A.relativeSpecCover.f U' = A.relativeSpecCover.f U := by
    have := colimit.w A.relativeSpecGluingData.functor i
    rw [A.relativeSpecGluingData_functor_map] at this
    exact this
  exact (Scheme.Hom.map_appLE_assoc _ _ _ _).trans
    (Scheme.Hom.appLE_ΓSpecIso_hom_naturality _ _ hι.symm _ _)

/-- Sections of the function algebra of `Spec_X A` above an affine open are the sections of `A`.

The isomorphism identifies the inverse image of the affine open `U` with the chart
`Spec Γ(A.X, U)`, then uses the ordinary identification of the global functions on a spectrum. -/
def relativeSpecCoverFunctionAlgebraSectionsRingEquiv (U : X.AffineZariskiSite) :
    Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, U.1) ≃+* Γ(A.X, U.1) :=
  (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv U.1).trans
    (@asIso _ _ _ _ (chartSectionsHom A U) (isIso_chartSectionsHom A U)).commRingCatIsoToRingEquiv

/-- Over an affine open `U`, the section comparison pulls a function back along the chart
`Spec Γ(A.X, U)` and evaluates it through `Scheme.ΓSpecIso`. -/
lemma relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply (U : X.AffineZariskiSite)
    (x : Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, U.1)) :
    A.relativeSpecCoverFunctionAlgebraSectionsRingEquiv U x =
      (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, U.1))).hom
        ((A.relativeSpecCover.f U).appLE _ ⊤ (A.top_le_preimage_relativeSpecToBase U)
          (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv U.1 x)) :=
  (rfl)

/-- The section comparisons over affine opens, as an isomorphism of presheaves of rings on the
small affine Zariski site. -/
private def affineSectionsIso :
    (toOpensFunctor X).op ⋙ A.relativeSpecToBase.pushforwardStructureAlgebra.sectionsPresheaf ≅
      (toOpensFunctor X).op ⋙ A.sectionsPresheaf :=
  Functor.isoWhiskerLeft _ A.relativeSpecToBase.pushforwardStructureAlgebraPresheafIso ≪≫
    NatIso.ofComponents
      (fun U ↦ @asIso _ _ _ _ (chartSectionsHom A U.unop) (isIso_chartSectionsHom A U.unop))
      (fun i ↦ chartSectionsHom_naturality A i.unop)

/-- The extension of the affine section comparisons to all opens, using that both presheaves
of rings are sheaves and that affine opens are cover-dense. -/
private def pushforwardSectionsPresheafIso :
    A.relativeSpecToBase.pushforwardStructureAlgebra.sectionsPresheaf ≅ A.sectionsPresheaf :=
  Functor.IsCoverDense.presheafIso (G := toOpensFunctor X) (K := Opens.grothendieckTopology X)
    (ℱ := ⟨_, isSheaf_sectionsPresheaf _⟩) (ℱ' := ⟨_, isSheaf_sectionsPresheaf A⟩)
    (affineSectionsIso A)

private lemma pushforwardSectionsPresheafIso_hom_app (U : X.AffineZariskiSite) :
    (pushforwardSectionsPresheafIso A).hom.app (op U.toOpens) =
      A.relativeSpecToBase.pushforwardStructureAlgebraPresheafIso.hom.app (op U.toOpens) ≫
        chartSectionsHom A U :=
  NatTrans.congr_app (Functor.IsCoverDense.sheafHom_restrict_eq
    (K := Opens.grothendieckTopology X) (ℱ' := ⟨_, isSheaf_sectionsPresheaf A⟩)
    (affineSectionsIso A).hom) (op U)

/-- The section comparison respects the structure maps from `𝒪ₓ`: over an affine open `U`, the
chart composed with the structure morphism is `Spec` of the structure map of `A`. -/
private lemma toSectionsPresheaf_comp_pushforwardSectionsPresheafIso_hom :
    A.relativeSpecToBase.pushforwardStructureAlgebra.toSectionsPresheaf ≫
      (pushforwardSectionsPresheafIso A).hom = A.toSectionsPresheaf := by
  suffices h : ∀ V : X.AffineZariskiSite,
      (A.relativeSpecToBase.pushforwardStructureAlgebra.toSectionsPresheaf ≫
        (pushforwardSectionsPresheafIso A).hom).app (op V.toOpens) =
      A.toSectionsPresheaf.app (op V.toOpens) from
    A.sectionsPresheaf_hom_ext fun U hU ↦ h ⟨U, hU⟩
  intro V
  have hc := NatTrans.congr_app
    A.relativeSpecToBase.pushforwardStructureAlgebra_toSectionsPresheaf_comp (op V.toOpens)
  rw [NatTrans.comp_app] at hc
  rw [NatTrans.comp_app, pushforwardSectionsPresheafIso_hom_app, reassoc_of% hc,
    chartSectionsHom]
  have h1 : A.relativeSpecToBase.app V.toOpens ≫ (A.relativeSpecCover.f V).appLE _ ⊤
        (A.top_le_preimage_relativeSpecToBase V) =
      (A.relativeSpecCover.f V ≫ A.relativeSpecToBase).appLE V.toOpens ⊤
        (A.top_le_preimage_relativeSpecToBase V) :=
    (Scheme.Hom.comp_appLE _ _ _ _ _).symm
  have h2 := Scheme.Hom.appLE_ΓSpecIso_hom_naturality V.2.fromSpec _
    (A.relativeSpecCover_f_relativeSpecToBase V) V.2.fromSpec_preimage_self.ge
    (A.top_le_preimage_relativeSpecToBase V)
  have h3 := (congrArg (· ≫ (Scheme.ΓSpecIso Γ(X, V.toOpens)).hom)
    (V.2.fromSpec_appLE_self V.2.fromSpec_preimage_self.ge)).trans (Iso.inv_hom_id _)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    (h2.trans ((congrArg (· ≫ _) h3).trans (Category.id_comp _))))

/-- The algebra-side unit of relative Spec: the function algebra `p_* 𝒪` of the relative
spectrum `p : Spec_X A ⟶ X` is isomorphic to `A`. Over each affine open `U`, it is the
identification of the functions on the chart `Spec Γ(A.X, U)` with `Γ(A.X, U)`
(`CategoryTheory.CommMon.sectionsAlgHom_relativeSpecPushforwardIso_hom_apply`). -/
def relativeSpecPushforwardIso : A.relativeSpecToBase.pushforwardStructureAlgebra ≅ A :=
  CommMon.isoOfSectionsPresheaf (pushforwardSectionsPresheafIso A)
    (toSectionsPresheaf_comp_pushforwardSectionsPresheafIso_hom A)

/-- Over an affine open, the isomorphism `p_* 𝒪 ≅ A` is the section comparison
`relativeSpecCoverFunctionAlgebraSectionsRingEquiv`. -/
-- Not a simp lemma: `CommMon.sectionsAlgHom_apply` already rewrites its left-hand side.
lemma sectionsAlgHom_relativeSpecPushforwardIso_hom_apply (U : X.AffineZariskiSite)
    (x : Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, U.1)) :
    CommMon.sectionsAlgHom A.relativeSpecPushforwardIso.hom U.1 x =
      A.relativeSpecCoverFunctionAlgebraSectionsRingEquiv U x := by
  have h := pushforwardSectionsPresheafIso_hom_app A U
  rw [Scheme.Hom.pushforwardStructureAlgebraPresheafIso_hom_app] at h
  rw [CommMon.sectionsAlgHom_apply, relativeSpecPushforwardIso, CommMon.isoOfSectionsPresheaf_hom,
    CommMon.homOfSectionsPresheaf_hom_hom_app_apply]
  exact congr($h x)

variable {A} {B : CommMon X.Modules} [B.X.IsQuasicoherent]

/-- The isomorphism `p_* 𝒪 ≅ A` is natural in the algebra: pulling back functions along
`Spec_X B ⟶ Spec_X A` corresponds to the algebra morphism `A ⟶ B`. -/
@[reassoc]
lemma relativeSpecPushforwardIso_hom_naturality (f : A ⟶ B) :
    Scheme.Hom.pushforwardStructureAlgebraMap (CommMon.relativeSpecMap f)
        (CommMon.relativeSpecMap_relativeSpecToBase f) ≫ B.relativeSpecPushforwardIso.hom =
      A.relativeSpecPushforwardIso.hom ≫ f := by
  refine CommMon.hom_ext_of_isAffineOpen fun U hU ↦ ?_
  suffices h : ∀ V : X.AffineZariskiSite, ∀ x,
      CommMon.sectionsAlgHom (Scheme.Hom.pushforwardStructureAlgebraMap
        (CommMon.relativeSpecMap f) (CommMon.relativeSpecMap_relativeSpecToBase f) ≫
          B.relativeSpecPushforwardIso.hom) V.1 x =
      CommMon.sectionsAlgHom (A.relativeSpecPushforwardIso.hom ≫ f) V.1 x from
    AlgHom.ext (h ⟨U, hU⟩)
  intro V x
  let g := CommMon.relativeSpecMap f
  have hle : B.relativeSpecToBase ⁻¹ᵁ V.toOpens ≤ g ⁻¹ᵁ (A.relativeSpecToBase ⁻¹ᵁ V.toOpens) := by
    rw [← Scheme.Hom.comp_preimage, CommMon.relativeSpecMap_relativeSpecToBase]
  -- On the charts over `V`, `g` is the spectrum of the algebra map `f` on sections.
  have hring : g.appLE _ _ hle ≫ chartSectionsHom B V =
      chartSectionsHom A V ≫ CommRingCat.ofHom (CommMon.sectionsAlgHom f V.toOpens).toRingHom :=
    (Scheme.Hom.appLE_comp_appLE_assoc (B.relativeSpecCover.f V) g _ _ ⊤ hle
      (B.top_le_preimage_relativeSpecToBase V) _).trans
        (Scheme.Hom.appLE_ΓSpecIso_hom_naturality _ _
          (CommMon.relativeSpecCover_f_relativeSpecMap f V) _ _)
  have hg := Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply g
    (CommMon.relativeSpecMap_relativeSpecToBase f) V.toOpens x
  rw [CommMon.sectionsAlgHom_comp, CommMon.sectionsAlgHom_comp, AlgHom.comp_apply,
    AlgHom.comp_apply, hg, sectionsAlgHom_relativeSpecPushforwardIso_hom_apply,
    sectionsAlgHom_relativeSpecPushforwardIso_hom_apply,
    relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply,
    relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply, RingEquiv.apply_symm_apply]
  exact congr($hring (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv
    V.toOpens x))

end

end CategoryTheory.CommMon

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- The algebra-side unit of relative Spec: a quasi-coherent algebra is naturally the function
algebra of its relative spectrum. -/
def relativeSpecUnit (X : Scheme.{u}) :
    𝟭 (QuasicoherentAlgebra X)ᵒᵖ ≅ relativeSpec X ⋙ affineFunctions X :=
  NatIso.ofComponents
    (fun A ↦ (ObjectProperty.isoMk _ A.unop.obj.relativeSpecPushforwardIso).op)
    (fun f ↦ by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      exact (CommMon.relativeSpecPushforwardIso_hom_naturality f.unop.hom).symm)

/-- The unit on underlying algebras is the isomorphism `p_* 𝒪 ≅ A`. -/
@[simp]
lemma relativeSpecUnit_hom_app_unop_hom {X : Scheme.{u}} (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpecUnit X).hom.app A).unop.hom = A.unop.obj.relativeSpecPushforwardIso.hom :=
  (rfl)

/-- The inverse unit on underlying algebras is the inverse of the isomorphism `p_* 𝒪 ≅ A`. -/
@[simp]
lemma relativeSpecUnit_inv_app_unop_hom {X : Scheme.{u}} (A : (QuasicoherentAlgebra X)ᵒᵖ) :
    ((relativeSpecUnit X).inv.app A).unop.hom = A.unop.obj.relativeSpecPushforwardIso.inv :=
  (rfl)

end

end TauCeti.AlgebraicGeometry

end
