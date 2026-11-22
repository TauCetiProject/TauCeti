/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pushforward and restriction of modules on schemes

Pushforward along a scheme isomorphism agrees with restriction along its inverse. This
identification transports local properties of module sheaves through affine normalizations.
Restriction of a pushforward to an open of the base agrees with pushforward of the restriction
to its preimage. Both comparisons have formulas on sections.

A module pushed forward from an open subscheme has only the zero section over any disjoint
open. This supplies the vanishing factors for products supported on disjoint open sets.

These comparisons use Mathlib's module pushforward and restriction API.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A module pushed forward from an open subscheme has only the zero section over a
disjoint open. -/
theorem subsingleton_sections_pushforward_of_disjoint {X : Scheme.{u}} {U V : X.Opens}
    (N : U.toScheme.Modules) (h : Disjoint V U) :
    Subsingleton Γ((pushforward U.ι).obj N, V) := by
  have hempty : U.ι ⁻¹ᵁ V = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    exact h.le_bot ⟨hx, x.property⟩
  rw [pushforward_obj_obj]
  exact hempty ▸ Module.subsingleton Γ(U.toScheme, ⊥) _

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Forgetting the module structure commutes with direct image. -/
lemma pushforward_comp_toSheaf (f : X ⟶ Y) :
    pushforward f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf =
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base :=
  (rfl)

/-- Forgetting the module structure commutes with direct image, on underlying presheaves: the
abelian presheaf of `f_* M` is the abelian presheaf of `M` precomposed with inverse image of
opens. -/
def pushforwardCompToPresheafIso (f : X ⟶ Y) :
    pushforward f ⋙ Scheme.Modules.toPresheaf Y ≅
      Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.base :=
  Functor.isoWhiskerLeft (pushforward f)
      (SheafOfModules.toSheafCompSheafToPresheafIso Y.ringCatSheaf).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (pushforward_comp_toSheaf f)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (TopCat.Sheaf.pushforwardForgetIso AddCommGrpCat.{u} f.base) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafOfModules.toSheafCompSheafToPresheafIso X.ringCatSheaf) _

/-- A function `r` on an open `U` of `Y` acts on sections of `f_* M` over `U` through `f.app U r`,
as a section of `M` over `f ⁻¹ᵁ U`. -/
lemma pushforward_obj_smul (f : X ⟶ Y) (M : X.Modules) {U : Y.Opens} (r : Γ(Y, U))
    (x : Γ((pushforward f).obj M, U)) :
    r • x = (f.app U r • show Γ(M, f ⁻¹ᵁ U) from x : Γ(M, f ⁻¹ᵁ U)) :=
  rfl

/-- Pushforward along an isomorphism agrees with restriction along its inverse. -/
def pushforwardIsoRestrictFunctor (e : X ≅ Y) : pushforward e.hom ≅ restrictFunctor e.inv := by
  refine SheafOfModules.pushforwardCongr₂ _
    (NatIso.ofComponents (fun V ↦ eqToIso (Scheme.Hom.inv_image e V)) (fun _ ↦ rfl)) ?_
  ext V x
  -- `pushforwardCongr₂` states coherence using ring-sheaf components; express these
  -- as scheme section maps so the open-immersion API applies.
  change (e.hom.app V.unop ≫ X.presheaf.map (eqToHom (Scheme.Hom.inv_image e V.unop)).op) x =
    (e.inv.appIso V.unop).inv x
  have h : e.hom.app V.unop = (e.inv.appIso V.unop).inv ≫
      X.presheaf.map (eqToHom (Scheme.Hom.inv_image e V.unop).symm).op := by
    refine (IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq e.hom e.inv (𝟙 X)
      e.hom_inv_id.symm V.unop).trans ?_
    -- The identity scheme's section map is definitionally the identity. Write the
    -- restriction with `inv_image` so its dependent source no longer contains `𝟙 X`.
    change (e.inv.appIso V.unop).inv ≫ (𝟙 _ ≫
      X.presheaf.map (eqToHom (Scheme.Hom.inv_image e V.unop).symm).op) = _
    rw [Category.id_comp]
  have hh : e.hom.app V.unop ≫
      X.presheaf.map (eqToHom (Scheme.Hom.inv_image e V.unop)).op =
      (e.inv.appIso V.unop).inv := by
    rw [h, Category.assoc, ← Functor.map_comp,
      Subsingleton.elim (_ ≫ _) (𝟙 _), CategoryTheory.Functor.map_id, Category.comp_id]
  exact congrArg (fun g : Γ(Y, V.unop) ⟶ Γ(X, e.inv ''ᵁ V.unop) ↦ g x) hh

/-- On sections, pushforward along an isomorphism is restriction along the equality
between the image under its inverse and the preimage under the forward map. -/
theorem pushforwardIsoRestrictFunctor_hom_app_val_app_apply (e : X ≅ Y) (M : X.Modules)
    (V : Y.Opens) (x : Γ((pushforward e.hom).obj M, V)) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((((pushforwardIsoRestrictFunctor e).hom.app M).val.app (.op V)) x =
      M.val.map (eqToHom (Scheme.Hom.inv_image e V)).op x) := by
  -- `pushforwardCongr₂` restricts sections along the components of `eqToIso`,
  -- whose underlying maps are `eqToHom`.
  rfl

/-- The inverse pushforward--restriction comparison uses the inverse equality of opens. -/
theorem pushforwardIsoRestrictFunctor_inv_app_val_app_apply (e : X ≅ Y) (M : X.Modules)
    (V : Y.Opens) (x : Γ(M.restrict e.inv, V)) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((((pushforwardIsoRestrictFunctor e).inv.app M).val.app (.op V)) x =
      M.val.map (eqToHom (Scheme.Hom.inv_image e V).symm).op x) := by
  -- The inverse components of `eqToIso` use the symmetric equality.
  rfl

/-- Restricting a pushforward to an open of the base agrees with pushing forward the
restriction to its preimage, naturally in the module sheaf. -/
def restrictPushforwardIso (f : X ⟶ Y) (U : Y.Opens) :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) := by
  -- Each composite is continuous via its intermediate open-scheme site; supplying these
  -- instances lets `SheafOfModules.pushforwardComp` elaborate the two composites.
  letI : (U.ι.opensFunctor ⋙ TopologicalSpace.Opens.map f.base).IsContinuous
      (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology Y) _
  letI : (TopologicalSpace.Opens.map (f ∣_ U).base ⋙ (f ⁻¹ᵁ U).ι.opensFunctor).IsContinuous
      (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (f ⁻¹ᵁ U).toScheme) _
  refine (SheafOfModules.pushforwardComp _ _) ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _
    (NatIso.ofComponents (fun V ↦ eqToIso (image_morphismRestrict_preimage f U V))
      (fun _ ↦ rfl)) ?_
  ext V x
  simp only [Scheme.Opens.ι_appIso]
  exact congrArg (fun g ↦ g x) (morphismRestrict_app f U V.unop).symm

-- Unfold `Functor.comp_obj` in the term: otherwise Lean cannot identify the section type
-- of the composite functor with that of the object-level restriction.
-- The components of `pushforwardComp` are identities on sections, and
-- `pushforwardCongr₂` with `eqToIso` is restriction along `eqToHom`, definitionally.
/-- On sections, open restriction of pushforward is the restriction along the equality
of the two inverse-image opens. -/
theorem restrictPushforwardIso_hom_app_val_app_apply (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) (V : U.toScheme.Opens)
    (x : Γ(((pushforward f).obj M).restrict U.ι, V)) :
    dsimp% only [Functor.comp_obj, sheafCompose_obj_obj, CommRingCat.forgetToRingCat_obj]
    ((((restrictPushforwardIso f U).hom.app M).val.app (.op V)) x =
      M.val.map (eqToHom (image_morphismRestrict_preimage f U V)).op x) :=
  (rfl)

/-- The inverse comparison restricts along the inverse equality of inverse-image opens. -/
theorem restrictPushforwardIso_inv_app_val_app_apply (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) (V : U.toScheme.Opens)
    (x : Γ((pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V)) :
    dsimp% only [Functor.comp_obj, sheafCompose_obj_obj, CommRingCat.forgetToRingCat_obj]
    ((((restrictPushforwardIso f U).inv.app M).val.app (.op V)) x =
      M.val.map (eqToHom (image_morphismRestrict_preimage f U V).symm).op x) :=
  (rfl)

/-- Pushing a morphism forward and identifying a factorized composite acts on sections by the
corresponding restriction along the equality of inverse-image opens. -/
lemma pushforward_composite_app {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (M : A.Modules) (N : B.Modules)
    (φ : N ⟶ (Scheme.Modules.pushforward a).obj M) (V : C.Opens)
    (s : Γ((Scheme.Modules.pushforward b).obj N, V)) :
    (((Scheme.Modules.pushforward b).map φ ≫
      (Scheme.Modules.pushforwardComp a b).hom.app M ≫
        (Scheme.Modules.pushforwardCongr h).hom.app M).app V s) =
      M.presheaf.map
        (eqToHom (show c ⁻¹ᵁ V = a ⁻¹ᵁ b ⁻¹ᵁ V from
          (congrArg (fun f ↦ f ⁻¹ᵁ V) h).symm.trans (Scheme.Hom.comp_preimage a b V))).op
          (φ.app (b ⁻¹ᵁ V) s) := rfl

/-- A compatible triangle of module morphisms remains compatible after pushing it along a further
scheme morphism, with the canonical comparisons for the resulting composites. -/
lemma pushforward_compatible {A B L S : Scheme.{u}}
    (a : A ⟶ L) (b : B ⟶ L) (t : L ⟶ S) (f : A ⟶ B)
    (pA : A ⟶ S) (pB : B ⟶ S)
    (hf : f ≫ b = a) (ha : a ≫ t = pA) (hb : b ≫ t = pB)
    (M : L.Modules) (N : A.Modules) (P : B.Modules)
    (πA : M ⟶ (Scheme.Modules.pushforward a).obj N)
    (πB : M ⟶ (Scheme.Modules.pushforward b).obj P)
    (τ : P ⟶ (Scheme.Modules.pushforward f).obj N)
    (hp : ∀ (W : L.Opens) (s : Γ(M, W)),
      N.presheaf.map (eqToHom (show a ⁻¹ᵁ W = f ⁻¹ᵁ b ⁻¹ᵁ W from
        (congrArg (fun g ↦ g ⁻¹ᵁ W) hf).symm.trans (Scheme.Hom.comp_preimage f b W))).op
        (τ.app (b ⁻¹ᵁ W) (πB.app W s)) = πA.app W s) :
    ((Scheme.Modules.pushforward t).map πB ≫
      (Scheme.Modules.pushforwardComp b t).hom.app P ≫
        (Scheme.Modules.pushforwardCongr hb).hom.app P) ≫
      (Scheme.Modules.pushforward pB).map τ ≫
        (Scheme.Modules.pushforwardComp f pB).hom.app N ≫
          (Scheme.Modules.pushforwardCongr
            (((Category.assoc f b t).trans (congrArg (f ≫ ·) hb)).symm.trans
              ((congrArg (· ≫ t) hf).trans ha))).hom.app N =
    (Scheme.Modules.pushforward t).map πA ≫
      (Scheme.Modules.pushforwardComp a t).hom.app N ≫
        (Scheme.Modules.pushforwardCongr ha).hom.app N := by
  apply Scheme.Modules.hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro s
  have hp' := hp (t ⁻¹ᵁ W) s
  -- The composite module morphism acts by successive application on sections.
  -- Stating the action explicitly avoids the two presentations of module composition.
  change (((Scheme.Modules.pushforward pB).map τ ≫
    (Scheme.Modules.pushforwardComp f pB).hom.app N ≫
      (Scheme.Modules.pushforwardCongr
            (((Category.assoc f b t).trans (congrArg (f ≫ ·) hb)).symm.trans
              ((congrArg (· ≫ t) hf).trans ha))).hom.app N).app W
      ((((Scheme.Modules.pushforward t).map πB ≫
        (Scheme.Modules.pushforwardComp b t).hom.app P ≫
          (Scheme.Modules.pushforwardCongr hb).hom.app P).app W s))) = _
  rw [pushforward_composite_app, pushforward_composite_app, pushforward_composite_app]
  have hn := NatTrans.naturality_apply τ.mapPresheaf
    (eqToHom (show pB ⁻¹ᵁ W = b ⁻¹ᵁ t ⁻¹ᵁ W from
      (congrArg (fun g ↦ g ⁻¹ᵁ W) hb).symm.trans (Scheme.Hom.comp_preimage b t W))).op
      (πB.app (t ⁻¹ᵁ W) s)
  simp only [Scheme.Modules.mapPresheaf_app, Scheme.Modules.pushforward_obj_presheaf_map]
    at hn
  rw [hn]
  erw [← Functor.map_comp_apply]
  rw [← hp']
  erw [← Functor.map_comp_apply]
  rfl

/-- Sectionwise bijectivity is preserved by pushforward and the comparison for a factorized
composite, evaluated at the corresponding inverse-image open. -/
lemma bijective_pushforward_composite_app {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (M : A.Modules) (N : B.Modules)
    (φ : N ⟶ (Scheme.Modules.pushforward a).obj M) (V : C.Opens)
    (hφ : Function.Bijective (φ.app (b ⁻¹ᵁ V))) :
    Function.Bijective (((Scheme.Modules.pushforward b).map φ ≫
      (Scheme.Modules.pushforwardComp a b).hom.app M ≫
        (Scheme.Modules.pushforwardCongr h).hom.app M).app V) := by
  rw [show ⇑(((Scheme.Modules.pushforward b).map φ ≫
      (Scheme.Modules.pushforwardComp a b).hom.app M ≫
        (Scheme.Modules.pushforwardCongr h).hom.app M).app V) = _ from
    funext (pushforward_composite_app a b c h M N φ V)]
  exact (ConcreteCategory.bijective_of_isIso _).comp hφ

/-- Transposing a composite pullback morphism agrees with transposing successively under the
two pullback--pushforward adjunctions and identifying the iterated pushforward. -/
lemma homEquiv_pullbackComp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (M : C.Modules) (N : A.Modules)
    (φ : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b)).homEquiv _ _
        ((Scheme.Modules.pullbackComp a b).inv.app M ≫ φ) =
      (((Scheme.Modules.pullbackPushforwardAdjunction b).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a)).homEquiv _ _ φ) ≫
          (Scheme.Modules.pushforwardComp a b).hom.app N := by
  have hu := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction a))
    (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b))
    (Scheme.Modules.pullbackComp a b).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← hu, Category.assoc,
    (Scheme.Modules.pushforwardComp a b).hom.naturality]

/-- The composite pullback adjunction formula also holds when the composite is identified with
an explicitly named scheme morphism. -/
lemma homEquiv_pullbackComp_congr {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (M : C.Modules) (N : A.Modules)
    (φ : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv _ _
        ((Scheme.Modules.pullbackCongr h).inv.app M ≫
          (Scheme.Modules.pullbackComp a b).inv.app M ≫ φ) =
      (((Scheme.Modules.pullbackPushforwardAdjunction b).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a)).homEquiv _ _ φ) ≫
          (Scheme.Modules.pushforwardComp a b).hom.app N ≫
            (Scheme.Modules.pushforwardCongr h).hom.app N := by
  subst h
  have hcongr : (Scheme.Modules.pushforwardCongr (rfl : a ≫ b = a ≫ b)).hom.app N = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro W
    simp only [Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.Hom.id_app]
    exact N.presheaf.map_id _
  rw [hcongr, Category.comp_id]
  simpa only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp] using homEquiv_pullbackComp a b M N φ

end

end TauCeti.AlgebraicGeometry
