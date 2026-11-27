/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.CategoryTheory.Sites.Pullback

/-!
# Extension from a localized site

The left adjoint to restriction from `C` to `Over U` sends a presheaf `F` to the presheaf
`X ↦ ∐ (f : X ⟶ U), F (Over.mk f)`. This only needs coproducts of the size of the hom types,
even when the site is large. Sheafifying gives the left adjoint on sheaves. When coproducts
are exact and sheafification is left exact, this left adjoint is exact.

## References

* Stacks Project, Section 18.19, Localization, especially Lemma 18.19.3 (03DJ).
-/

public section

open CategoryTheory Limits Opposite

universe u v w w'

namespace TauCeti.CategoryTheory.Over

noncomputable section

variable {C : Type u} [Category.{v} C] (U : C)
  {A : Type w} [Category.{w'} A] [HasCoproducts.{v} A]

private def extensionMap (F : (Over U)ᵒᵖ ⥤ A) {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    (∐ fun f : X.unop ⟶ U ↦ F.obj (op (Over.mk f))) ⟶
      ∐ fun f : Y.unop ⟶ U ↦ F.obj (op (Over.mk f)) :=
  Limits.Sigma.map' (fun f : X.unop ⟶ U ↦ g.unop ≫ f)
    (fun f ↦ F.map (Over.homMk g.unop rfl : Over.mk (g.unop ≫ f) ⟶ Over.mk f).op)

private lemma ι_extensionMap (F : (Over U)ᵒᵖ ⥤ A) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (f : X.unop ⟶ U) (h : Y.unop ⟶ U) (e : g.unop ≫ f = h) :
    Sigma.ι (fun f : X.unop ⟶ U ↦ F.obj (op (Over.mk f))) f ≫ extensionMap U F g =
      F.map (Over.homMk g.unop e : Over.mk h ⟶ Over.mk f).op ≫
        Sigma.ι (fun h : Y.unop ⟶ U ↦ F.obj (op (Over.mk h))) h := by
  subst h
  simp [extensionMap]

private def extensionObj (F : (Over U)ᵒᵖ ⥤ A) : Cᵒᵖ ⥤ A where
  obj X := ∐ fun f : X.unop ⟶ U ↦ F.obj (op (Over.mk f))
  map := extensionMap U F
  map_id X := by
    apply Sigma.hom_ext
    intro f
    rw [ι_extensionMap U F (𝟙 X) f f (Category.id_comp f)]
    -- With the coproduct index fixed, the over-morphism is the identity.
    change F.map (𝟙 _) ≫ _ = _
    simp
  map_comp g h := by
    apply Sigma.hom_ext
    intro f
    rw [← Category.assoc, ι_extensionMap U F g f _ rfl, Category.assoc,
      ι_extensionMap U F h (g.unop ≫ f) ((h.unop ≫ g.unop) ≫ f)
        (Category.assoc _ _ _).symm,
      ι_extensionMap U F (g ≫ h) f _ rfl, ← Category.assoc, ← F.map_comp]
    rfl

/-- Extension of presheaves from `Over U`, given at `X` by the coproduct over maps `X ⟶ U`. -/
def presheafExtension : ((Over U)ᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A where
  obj := extensionObj U
  map α :=
    { app := fun X ↦ Limits.Sigma.map fun f : X.unop ⟶ U ↦ α.app (op (Over.mk f))
      naturality := by
        intro X Y g
        apply Sigma.hom_ext
        intro f
        dsimp only [extensionObj]
        rw [← Category.assoc, ι_extensionMap U _ g f _ rfl]
        simp only [Category.assoc, Sigma.ι_map_assoc]
        simp only [Sigma.ι_map]
        rw [← Category.assoc, α.naturality]
        simp [extensionMap] }
  map_id F := by
    ext X
    dsimp only [extensionObj]
    apply Sigma.hom_ext
    intro f
    simp
  map_comp α β := by
    ext X
    dsimp only [extensionObj]
    apply Sigma.hom_ext
    intro f
    simp

/-- The coproduct injection into the extension indexed by a map `f : X ⟶ U`. -/
def presheafExtensionι (F : (Over U)ᵒᵖ ⥤ A) {X : C} (f : X ⟶ U) :
    F.obj (op (Over.mk f)) ⟶ ((presheafExtension U).obj F).obj (op X) :=
  Sigma.ι (fun f : X ⟶ U ↦ F.obj (op (Over.mk f))) f

/-- Restriction in the extension sends the `f` summand to the `g ≫ f` summand. -/
@[reassoc (attr := simp)]
lemma presheafExtensionι_map (F : (Over U)ᵒᵖ ⥤ A) {X Y : C}
    (g : Y ⟶ X) (f : X ⟶ U) :
    presheafExtensionι U F f ≫ ((presheafExtension U).obj F).map g.op =
      F.map (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f).op ≫
        presheafExtensionι U F (g ≫ f) :=
  ι_extensionMap U F g.op f _ rfl

/-- Extension acts on a natural transformation separately on each coproduct summand. -/
@[reassoc (attr := simp)]
lemma presheafExtensionι_map_app {F G : (Over U)ᵒᵖ ⥤ A} (α : F ⟶ G)
    {X : C} (f : X ⟶ U) :
    presheafExtensionι U F f ≫ ((presheafExtension U).map α).app (op X) =
      α.app (op (Over.mk f)) ≫ presheafExtensionι U G f := by
  dsimp only [presheafExtensionι, presheafExtension, extensionObj]
  simp only [Sigma.ι_map]

private def restrictHom {F : (Over U)ᵒᵖ ⥤ A} {G : Cᵒᵖ ⥤ A}
    (α : (presheafExtension U).obj F ⟶ G) : F ⟶ (Over.forget U).op ⋙ G where
  app Y := Sigma.ι (fun f : Y.unop.left ⟶ U ↦ F.obj (op (Over.mk f))) Y.unop.hom ≫
    α.app (op Y.unop.left)
  naturality Y Z g := by
    -- Present the over-objects as `mk` objects so the coproduct summands have the same types.
    obtain ⟨⟨Y, ⟨⟨⟩⟩, fY⟩⟩ := Y
    obtain ⟨⟨Z, ⟨⟨⟩⟩, fZ⟩⟩ := Z
    dsimp only [presheafExtension, extensionObj] at α
    have h := congrArg (fun k ↦
      Sigma.ι (fun f : Y ⟶ U ↦ F.obj (op (Over.mk f))) fY ≫ k)
      (α.naturality ((Over.forget U).op.map g))
    dsimp only [presheafExtension, extensionObj] at h
    rw [← Category.assoc] at h
    erw [ι_extensionMap U F ((Over.forget U).op.map g) fY fZ
      (Over.w g.unop)] at h
    simp only [Category.assoc] at h ⊢
    exact h

private def extendHom {F : (Over U)ᵒᵖ ⥤ A} {G : Cᵒᵖ ⥤ A}
    (α : F ⟶ (Over.forget U).op ⋙ G) : (presheafExtension U).obj F ⟶ G where
  app X := Sigma.desc fun f : X.unop ⟶ U ↦ α.app (op (Over.mk f))
  naturality X Y g := by
    apply Sigma.hom_ext
    intro f
    simp [presheafExtension, extensionObj, extensionMap]

/-- The coproduct extension of presheaves is left adjoint to restriction to `Over U`. -/
def presheafExtensionAdjunction : presheafExtension (A := A) U ⊣
    (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ A).obj (Over.forget U).op :=
  Adjunction.mkOfHomEquiv
    { homEquiv F G :=
        { toFun := restrictHom U
          invFun := extendHom U
          left_inv α := by
            ext X
            apply Sigma.hom_ext
            intro f
            simp [extendHom, restrictHom]
          right_inv α := by
            ext Y
            simp only [restrictHom, extendHom, Sigma.ι_comp_desc]
            congr 1 }
      homEquiv_naturality_left_symm := by
        intro F F' G α β
        -- Unfold the hom-equivalence projection to compare the coproduct descents.
        change extendHom U (α ≫ β) = (presheafExtension U).map α ≫ extendHom U β
        ext X
        apply Sigma.hom_ext
        intro f
        dsimp only [extendHom, presheafExtension, extensionObj, NatTrans.comp_app]
        rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_comp_desc,
          Sigma.ι_comp_desc]
      homEquiv_naturality_right := by
        intro F G G' α β
        ext Y
        -- The hom-equivalence is restriction along a coproduct injection.
        change (restrictHom U (α ≫ β)).app Y =
          (restrictHom U α).app Y ≫ β.app (op Y.unop.left)
        exact (Category.assoc _ _ _).symm }

-- Avoid indexing the hom-equivalence coercions, whose functor-type projections can have
-- different normal forms in importing modules.
/-- The adjunction restricts a map by precomposing with the corresponding coproduct injection. -/
@[simp]
lemma presheafExtensionAdjunction_homEquiv_app {F : (Over U)ᵒᵖ ⥤ A} {G : Cᵒᵖ ⥤ A}
    (α : (presheafExtension U).obj F ⟶ G) (Y : (Over U)ᵒᵖ) :
    (no_index ((presheafExtensionAdjunction U).homEquiv F G α)).app Y =
      presheafExtensionι U F Y.unop.hom ≫ α.app (op Y.unop.left) := by
  simp only [presheafExtensionAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The inverse adjunction map has the prescribed component on each coproduct summand. -/
@[reassoc (attr := simp)]
lemma presheafExtensionι_homEquiv_symm_app {F : (Over U)ᵒᵖ ⥤ A} {G : Cᵒᵖ ⥤ A}
    (α : F ⟶ (Over.forget U).op ⋙ G) {X : C} (f : X ⟶ U) :
    presheafExtensionι U F f ≫
        (no_index (((presheafExtensionAdjunction U).homEquiv F G).symm α)).app (op X) =
      α.app (op (Over.mk f)) := by
  simp only [presheafExtensionAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  dsimp only [Equiv.symm, Equiv.coe_fn_mk, extendHom, presheafExtensionι]
  exact Sigma.ι_comp_desc _ _

/-- Evaluating extension at `X` is the coproduct of evaluations at the objects `(X, f)`. -/
def presheafExtensionEvaluationIso (X : C) :
    presheafExtension (A := A) U ⋙ (evaluation Cᵒᵖ A).obj (op X) ≅
      (Functor.whiskeringLeft _ _ A).obj
        (Discrete.functor fun f : X ⟶ U ↦ op (Over.mk f)) ⋙ colim :=
  NatIso.ofComponents (fun F ↦ HasColimit.isoOfNatIso
    (Discrete.compNatIsoDiscrete (fun f : X ⟶ U ↦ op (Over.mk f)) F).symm) (by
      intro F G α
      dsimp [presheafExtension, extensionObj]
      cat_disch)

/-- Extension of presheaves from a slice preserves finite limits when coproducts are exact. -/
instance [HasFiniteLimits A] [AB4OfSize.{v} A] :
    PreservesFiniteLimits (presheafExtension (A := A) U) := by
  refine preservesFiniteLimits_of_evaluation _ fun X ↦ ?_
  have := HasExactColimitsOfShape.preservesFiniteLimits (J := Discrete (X.unop ⟶ U)) (C := A)
  exact preservesFiniteLimits_of_natIso (presheafExtensionEvaluationIso U X.unop).symm

variable (J : GrothendieckTopology C) [HasWeakSheafify J A]

private def sheafExtension : Sheaf (J.over U) A ⥤ Sheaf J A :=
  sheafToPresheaf (J.over U) A ⋙ presheafExtension U ⋙ presheafToSheaf J A

private def sheafExtensionAdjunction : sheafExtension (A := A) U J ⊣ J.overPullback A U :=
  ((presheafExtensionAdjunction U).comp (sheafificationAdjunction J A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (J.over U) A) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

/-- Restriction to a localized site has a left adjoint if the coefficient category has
coproducts of the size of the hom types and the ambient site admits sheafification. -/
instance isRightAdjoint_overPullback : (J.overPullback A U).IsRightAdjoint :=
  (sheafExtensionAdjunction U J).isRightAdjoint

/-- Extension from a localized site is computed by sheafifying the coproduct extension. -/
def sheafPullbackIsoPresheafExtension :
    (Over.forget U).sheafPullback A (J.over U) J ≅
      sheafToPresheaf (J.over U) A ⋙ presheafExtension U ⋙ presheafToSheaf J A :=
  ((Over.forget U).sheafAdjunctionContinuous A (J.over U) J).leftAdjointUniq
    (sheafExtensionAdjunction U J)

omit [HasWeakSheafify J A] in
/-- Extension from a localized site preserves finite limits when coproducts are exact. -/
instance preservesFiniteLimits_sheafPullback [HasFiniteLimits A] [AB4OfSize.{v} A]
    [HasSheafify J A] :
    PreservesFiniteLimits ((Over.forget U).sheafPullback A (J.over U) J) := by
  have : PreservesFiniteLimits (sheafExtension (A := A) U J) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (sheafPullbackIsoPresheafExtension U J).symm

end

end TauCeti.CategoryTheory.Over
