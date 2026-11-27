/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Monoidal.Functor
public import TauCeti.CategoryTheory.Sites.Monoidal

/-!
# Monoidal structure of sheaf pushforward and pullback

Let `A` be a monoidal category and `u : (C, J) ⥤ (D, K)` a continuous functor between sites.
Equip `Sheaf J A` and `Sheaf K A` with the tensor product obtained by sheafifying the sectionwise
tensor product (`CategoryTheory.Sheaf.monoidalCategory`). The pushforward
`u_* = u.sheafPushforwardContinuous A J K` is the sheafification of the restriction of underlying
presheaves along `u`, so it is lax monoidal: its tensor map `u_* F ⊗ u_* G ⟶ u_* (F ⊗ G)` is
induced by `Sheaf.toTensorObj F G` restricted along `u`, and its unit map by `Sheaf.toTensorUnit`.
When `u_*` has a left adjoint, the pullback `u^* = u.sheafPullback A J K`, Mathlib's
`Adjunction.leftAdjointOplaxMonoidal` makes `u^*` oplax monoidal, with tensor comparison
`u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G` adjoint to the units of `u^* ⊣ u_*` followed by the tensor map of
`u_*`.

## Main declarations

* `CategoryTheory.Functor.sheafPushforwardContinuousLaxMonoidal`: the lax monoidal structure on
  `u.sheafPushforwardContinuous A J K`, whose tensor and unit maps are characterised by
  `CategoryTheory.Functor.toTensorObj_comp_sheafPushforwardContinuous_μ_hom` and
  `CategoryTheory.Functor.toTensorUnit_comp_sheafPushforwardContinuous_ε_hom`.
* `CategoryTheory.Functor.sheafPullbackOplaxMonoidal`: the oplax monoidal structure on
  `u.sheafPullback A J K`, the left adjoint of the lax monoidal pushforward.
* `CategoryTheory.Functor.toTensorObj_app_comp_unit_app_comp_sheafPullback_δ_app`: on sections,
  the tensor comparison of `u^*` sends the image of `F.obj ⊗ G.obj` under the unit of
  `u^* ⊣ u_*` to the tensor product of the units.
* `CategoryTheory.Functor.toTensorUnit_app_comp_unit_app_comp_sheafPullback_η_app`: the same
  sections formula for the unit comparison of `u^*`.
-/

public section

open CategoryTheory Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Functor

attribute [local instance] Sheaf.monoidalCategory

variable {C D : Type*} [Category* C] [Category* D] (u : C ⥤ D) (A : Type*) [Category* A]
  [MonoidalCategory A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [u.IsContinuous J K]

/-- The pushforward of sheaves along `u` is lax monoidal. On underlying presheaves it is the
restriction along `u`, which is strict monoidal, and `sheafToPresheaf J A` is lax monoidal as the
right adjoint of the monoidal sheafification; sheafifying again recovers `u_*` through
`sheafificationIso`. Its tensor and unit maps are characterised by
`toTensorObj_comp_sheafPushforwardContinuous_μ_hom` and
`toTensorUnit_comp_sheafPushforwardContinuous_ε_hom`. -/
noncomputable instance sheafPushforwardContinuousLaxMonoidal :
    (u.sheafPushforwardContinuous A J K).LaxMonoidal :=
  letI := (sheafificationAdjunction K A).rightAdjointLaxMonoidal
  letI : (u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A).LaxMonoidal :=
    Functor.LaxMonoidal.transport (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  Functor.LaxMonoidal.transport (F := (u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A) ⋙
      presheafToSheaf J A) (associator _ _ _ ≪≫
    isoWhiskerLeft _ (sheafificationNatIso J A).symm ≪≫ rightUnitor _)

/-- The tensor map of the pushforward of sheaves along `u` restricts along `Sheaf.toTensorObj` to
the restriction of `Sheaf.toTensorObj` along `u`; by `Sheaf.tensorObj_hom_ext` this characterises
it. -/
@[reassoc]
lemma toTensorObj_comp_sheafPushforwardContinuous_μ_hom (F G : Sheaf K A) :
    Sheaf.toTensorObj ((u.sheafPushforwardContinuous A J K).obj F)
        ((u.sheafPushforwardContinuous A J K).obj G) ≫
      (μ (u.sheafPushforwardContinuous A J K) F G).hom =
    Functor.whiskerLeft u.op (Sheaf.toTensorObj F G) := by
  let := (sheafificationAdjunction K A).rightAdjointLaxMonoidal
  have hS : μ (sheafToPresheaf K A) F G = Sheaf.toTensorObj F G := by
    have hc (H : Sheaf K A) :
        (sheafificationAdjunction K A).counit.app H = (sheafificationIso H).inv := by
      ext1
      simp
    rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit, hc, hc]
    simp [Sheaf.toTensorObj_def]
  let : (u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A).LaxMonoidal :=
    Functor.LaxMonoidal.transport (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  rw [sheafPushforwardContinuousLaxMonoidal, LaxMonoidal.transport_μ, comp_μ,
    LaxMonoidal.transport_μ, comp_μ, hS]
  have hN (P : Sheaf J A) : (sheafificationNatIso J A).hom.app P = (sheafificationIso P).hom :=
    (rfl)
  have hN' (P : Sheaf J A) : (sheafificationNatIso J A).inv.app P = (sheafificationIso P).inv :=
    (rfl)
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, associator_inv_app,
    associator_hom_app, isoWhiskerLeft_inv, isoWhiskerLeft_hom, whiskerLeft_app,
    rightUnitor_inv_app, rightUnitor_hom_app, Iso.symm_inv, Iso.symm_hom, hN, hN',
    Category.id_comp, Category.comp_id]
  rw [Sheaf.toTensorObj_def, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom]
  -- Restriction along `u.op` is strict monoidal: its tensor map is the identity by definition.
  have hW : μ ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op) F.obj G.obj = 𝟙 _ := (rfl)
  simp only [Monoidal.μIso_inv, comp_obj, ObjectProperty.ι_obj, whiskeringLeft_obj_obj,
    whiskeringLeft_obj_map, Category.assoc, map_comp, id_obj, Category.comp_id,
    tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, tensorHom_id, id_whiskerRight,
    Category.id_comp, Monoidal.δ_μ_assoc, ObjectProperty.FullSubcategory.comp_hom,
    sheafificationIso_inv_hom, isoSheafify_inv, sheafifyMap_sheafifyLift, toSheafify_sheafifyLift,
    sheafPushforwardContinuousCompSheafToPresheafIso, Iso.refl_hom, Iso.refl_inv]
  -- The identities are typed through `(u.sheafPushforwardContinuous A J K).obj F).obj`, which is
  -- `u.op ⋙ F.obj` only after unfolding `Functor.sheafPushforwardContinuous`.
  erw [id_tensorHom_id, Category.id_comp, hW, Category.id_comp, Category.comp_id]

/-- The unit map of the pushforward of sheaves along `u` restricts along `Sheaf.toTensorUnit` to
the restriction of `Sheaf.toTensorUnit` along `u`; by `Sheaf.tensorUnit_hom_ext` this
characterises it. -/
@[reassoc]
lemma toTensorUnit_comp_sheafPushforwardContinuous_ε_hom :
    Sheaf.toTensorUnit J A ≫ (ε (u.sheafPushforwardContinuous A J K)).hom =
      Functor.whiskerLeft u.op (Sheaf.toTensorUnit K A) := by
  let := (sheafificationAdjunction K A).rightAdjointLaxMonoidal
  have hS : ε (sheafToPresheaf K A) = Sheaf.toTensorUnit K A := by
    rw [Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
    simp [Sheaf.toTensorUnit_def]
  let : (u.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A).LaxMonoidal :=
    Functor.LaxMonoidal.transport (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
  rw [sheafPushforwardContinuousLaxMonoidal, LaxMonoidal.transport_ε, comp_ε,
    LaxMonoidal.transport_ε, comp_ε, hS]
  have hN' (P : Sheaf J A) : (sheafificationNatIso J A).inv.app P = (sheafificationIso P).inv :=
    (rfl)
  simp only [Iso.trans_hom, NatTrans.comp_app, associator_hom_app, isoWhiskerLeft_hom,
    whiskerLeft_app, rightUnitor_hom_app, Iso.symm_hom, hN', Category.id_comp]
  rw [Sheaf.toTensorUnit_def, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom]
  -- Restriction along `u.op` is strict monoidal: its unit map is the identity by definition.
  have hW : ε ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op) = 𝟙 _ := (rfl)
  simp only [Monoidal.εIso_inv, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    sheafificationIso_inv_hom, isoSheafify_inv, hW, Category.id_comp, whiskeringLeft_obj_map,
    sheafPushforwardContinuousCompSheafToPresheafIso, Iso.refl_inv]
  rw [← Category.assoc (η (presheafToSheaf J A)).hom, ← ObjectProperty.FullSubcategory.comp_hom,
    Monoidal.η_ε]
  have hU := (sheafificationAdjunction J A).unit.naturality
    (u.op.whiskerLeft (Sheaf.toTensorUnit K A))
  simp only [id_obj, comp_obj, sheafificationAdjunction_unit_app, comp_map, id_map] at hU
  simp only [NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom, Category.id_comp]
  -- The identities are typed through `(u.sheafPushforwardContinuous A J K).obj _`, and `hU`
  -- through `presheafToSheaf J A` composed with `sheafToPresheaf J A`: these agree with the goal
  -- only after unfolding `Functor.sheafPushforwardContinuous` and `sheafToPresheaf`.
  erw [Category.comp_id, Category.comp_id, ← reassoc_of% hU, toSheafify_sheafifyLift,
    Category.comp_id]

variable [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The pullback of sheaves along `u` is oplax monoidal, as the left adjoint of the lax monoidal
pushforward (`Adjunction.leftAdjointOplaxMonoidal`). -/
noncomputable instance sheafPullbackOplaxMonoidal : (u.sheafPullback A J K).OplaxMonoidal :=
  (u.sheafAdjunctionContinuous A J K).leftAdjointOplaxMonoidal

/-- The adjunction `u^* ⊣ u_*` is compatible with the oplax monoidal structure of the pullback and
the lax monoidal structure of the pushforward. -/
instance isMonoidal_sheafAdjunctionContinuous : (u.sheafAdjunctionContinuous A J K).IsMonoidal :=
  inferInstanceAs (letI := (u.sheafAdjunctionContinuous A J K).leftAdjointOplaxMonoidal
    (u.sheafAdjunctionContinuous A J K).IsMonoidal)

/-- Over `X : C`, the comparison `Sheaf.toTensorObj F G` followed by the unit of `u^* ⊣ u_*` at
`F ⊗ G` and the tensor comparison of `u^*` is the tensor product of the units at `F` and `G`
followed by `Sheaf.toTensorObj` over `u X`. -/
@[reassoc]
lemma toTensorObj_app_comp_unit_app_comp_sheafPullback_δ_app (F G : Sheaf J A) (X : C) :
    (Sheaf.toTensorObj F G).app (op X) ≫
        ((u.sheafAdjunctionContinuous A J K).unit.app (F ⊗ G)).hom.app (op X) ≫
          (δ (u.sheafPullback A J K) F G).hom.app (op (u.obj X)) =
      (((u.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op X) ⊗ₘ
          ((u.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X)) ≫
        (Sheaf.toTensorObj _ _).app (op (u.obj X)) := by
  have h := congrArg (Sheaf.toTensorObj F G ≫ ·.hom)
    ((u.sheafAdjunctionContinuous A J K).unit_app_tensor_comp_map_δ F G)
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ← Sheaf.toTensorObj_naturality_assoc] at h
  dsimp only [Functor.comp_obj] at h
  rw [toTensorObj_comp_sheafPushforwardContinuous_μ_hom] at h
  have h' := congr_app h (op X)
  simp only [NatTrans.comp_app] at h'
  -- `h'` is the goal up to definitional unfolding: the sections of `u_* (u^* F ⊗ u^* G)` over `X`
  -- are those of `u^* F ⊗ u^* G` over `u X` (`Functor.sheafPushforwardContinuous`), and tensor
  -- products and whiskerings of natural transformations are computed objectwise.
  exact h'

/-- Over `X : C`, the comparison `Sheaf.toTensorUnit J A` followed by the unit of `u^* ⊣ u_*` at
`𝟙_ (Sheaf J A)` and the unit comparison of `u^*` is `Sheaf.toTensorUnit K A` over `u X`. -/
@[reassoc]
lemma toTensorUnit_app_comp_unit_app_comp_sheafPullback_η_app (X : C) :
    (Sheaf.toTensorUnit J A).app (op X) ≫
        ((u.sheafAdjunctionContinuous A J K).unit.app (𝟙_ (Sheaf J A))).hom.app (op X) ≫
          (η (u.sheafPullback A J K)).hom.app (op (u.obj X)) =
      (Sheaf.toTensorUnit K A).app (op (u.obj X)) := by
  have h := congrArg (Sheaf.toTensorUnit J A ≫ ·.hom)
    (u.sheafAdjunctionContinuous A J K).unit_app_unit_comp_map_η
  rw [ObjectProperty.FullSubcategory.comp_hom,
    toTensorUnit_comp_sheafPushforwardContinuous_ε_hom] at h
  -- As for `δ`, `h` is the goal up to definitional unfolding of the sections of `u_*`.
  exact congr_app h (op X)

end CategoryTheory.Functor
