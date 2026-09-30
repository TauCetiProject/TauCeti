/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Pushforward of sheaves of modules is lax monoidal

Let `F : C ⥤ D` be a continuous functor between small sites, `R` and `S` sheaves of commutative
rings on `D` and `C`, and `φ : S ⟶ F_* R` a morphism of the underlying sheaves of rings. This file
equips the pushforward `SheafOfModules.pushforward φ` of sheaves of modules with its canonical lax
monoidal structure, whose tensor map `φ_* M ⊗ φ_* N ⟶ φ_* (M ⊗ N)` is induced by the sectionwise
map `m ⊗ n ↦ m ⊗ n`, and whose unit map is Mathlib's `SheafOfModules.unitToPushforwardObjUnit φ`.
Consequently the pullback functor, the left adjoint of the pushforward, is oplax monoidal: it
carries comparison maps `φ^* (M ⊗ N) ⟶ φ^* M ⊗ φ^* N` and `φ^* S ⟶ R`, the latter being
Mathlib's `SheafOfModules.pullbackObjUnitToUnit φ`.

The construction proceeds in three steps.

* The inclusion `SheafOfModules.forget` of sheaves of modules into presheaves of modules is right
  adjoint to sheafification, which is monoidal; so the inclusion is lax monoidal
  (`SheafOfModules.forgetLaxMonoidal`), its tensor map being the unit of sheafification
  `M.val ⊗ N.val ⟶ (M ⊗ N).val`.
* The pushforward of sheaves of modules is isomorphic to the composite of the inclusion, the
  pushforward of presheaves of modules, and sheafification
  (`SheafOfModules.presheafPushforwardSheafificationIso`). All three are lax monoidal, the middle
  one sectionwise (`TauCeti.PresheafOfModules.pushforwardLaxMonoidal`), and the lax monoidal
  structure transports along the isomorphism (`CategoryTheory.Functor.LaxMonoidal.transport`).
* The left adjoint of a lax monoidal functor is oplax monoidal
  (`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`).

## Main declarations

* `SheafOfModules.forgetLaxMonoidal`, with `SheafOfModules.forget_ε` and
  `SheafOfModules.forget_μ`;
* `SheafOfModules.presheafPushforward`: the pushforward of presheaves of modules underlying the
  pushforward of sheaves of modules, with its lax monoidal structure;
* `SheafOfModules.pushforwardLaxMonoidal`, with `SheafOfModules.pushforward_ε` and
  `SheafOfModules.pushforward_μ`;
* `SheafOfModules.pullbackOplaxMonoidal`, with `SheafOfModules.pullback_η`.

## References

* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of a tensor product), which
  shows that the comparison map of pullback constructed here is an isomorphism.
-/

public section

open CategoryTheory Category MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

section Forget

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- Sheafification of presheaves of modules is left adjoint to the inclusion
`SheafOfModules.forget` of sheaves of modules. This is Mathlib's
`PresheafOfModules.sheafificationAdjunction` along the identity of the sheaf of rings, whose
right adjoint `forget ⋙ restrictScalars (𝟙 _)` is definitionally `forget`. -/
def sheafificationForgetAdjunction :
    PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj) ⊣
      _root_.SheafOfModules.forget (ringCatSheaf R) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)

/-- The counit of `sheafificationForgetAdjunction` at a sheaf of modules `M` is the
identification `sheafificationIso` of the sheafification of `M.val` with `M`. -/
lemma sheafificationForgetAdjunction_counit_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (sheafificationForgetAdjunction R).counit.app M = (sheafificationIso _ M).hom :=
  (sheafificationIso_hom _ M).symm

/-- The inclusion of sheaves of modules into presheaves of modules is lax monoidal, as the right
adjoint of the monoidal functor sheafification. Its tensor map `M.val ⊗ N.val ⟶ (M ⊗ N).val` is
the unit of sheafification (`SheafOfModules.forget_μ`), and its unit map is the identity
(`SheafOfModules.forget_ε`). -/
instance forgetLaxMonoidal : (_root_.SheafOfModules.forget (ringCatSheaf R)).LaxMonoidal :=
  (sheafificationForgetAdjunction R).rightAdjointLaxMonoidal

/-- The unit map of the inclusion of sheaves of modules into presheaves of modules is the
identity. -/
@[simp]
lemma forget_ε : Functor.LaxMonoidal.ε (_root_.SheafOfModules.forget (ringCatSheaf R)) = 𝟙 _ := by
  have h : (sheafificationUnitIso R).hom =
      (sheafificationForgetAdjunction R).counit.app (𝟙_ _) :=
    sheafificationUnitIso_hom R
  rw [forgetLaxMonoidal, Adjunction.rightAdjointLaxMonoidal_ε, sheafification_η, h]
  exact ((sheafificationForgetAdjunction R).homEquiv_unit _ _ _).trans
    ((sheafificationForgetAdjunction R).right_triangle_components (𝟙_ _))

/-- The tensor map `M.val ⊗ N.val ⟶ (M ⊗ N).val` of the inclusion of sheaves of modules into
presheaves of modules is the unit of sheafification, followed by the identification
`tensorUnderlyingIso` of `M ⊗ N` with the sheafification of `M.val ⊗ N.val`. -/
lemma forget_μ (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N =
      (sheafificationForgetAdjunction R).unit.app (M.val ⊗ N.val) ≫
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map (M.tensorUnderlyingIso N).inv := by
  rw [forgetLaxMonoidal, Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit,
    SheafOfModules.tensorUnderlyingIso_inv, ← sheafificationForgetAdjunction_counit_app,
    ← sheafificationForgetAdjunction_counit_app]
  rfl

end Forget

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))

/-- The morphism of presheaves of commutative rings underlying `φ`. -/
private def commRingCatHom : S.obj ⟶ F.op ⋙ R.obj where
  app U := CommRingCat.ofHom (φ.hom.app U).hom
  naturality _ _ f := by
    ext x
    exact congr($(φ.hom.naturality f).hom x)

/-- The pushforward of presheaves of modules underlying `SheafOfModules.pushforward φ`. It is
Mathlib's `PresheafOfModules.pushforward φ.hom`, with source and target written as presheaves of
modules over the presheaves of rings `(ringCatSheaf R).obj` and `(ringCatSheaf S).obj`, so that it
composes with `SheafOfModules.forget` and with sheafification. -/
@[expose]
def presheafPushforward :
    PresheafOfModules.{u} (ringCatSheaf R).obj ⥤ PresheafOfModules.{u} (ringCatSheaf S).obj :=
  PresheafOfModules.pushforward φ.hom

/-- The pushforward of presheaves of modules is lax monoidal, sectionwise
(`TauCeti.PresheafOfModules.pushforwardLaxMonoidal`). It is characterized by
`presheafPushforward_ε_app_apply` and `presheafPushforward_μ_app_tmul`. -/
-- A definition rather than an `instance`, whose body would be exported, so that its body may use
-- the private `commRingCatHom`.
@[instance_reducible]
def presheafPushforwardLaxMonoidal : (presheafPushforward φ).LaxMonoidal :=
  PresheafOfModules.pushforwardLaxMonoidal F (commRingCatHom φ)

attribute [instance] presheafPushforwardLaxMonoidal

/-- On sections over `U`, the unit map of the pushforward of presheaves of modules is `φ`. -/
@[simp]
lemma presheafPushforward_ε_app_apply (U : Cᵒᵖ) (r : S.obj.obj U) :
    (Functor.LaxMonoidal.ε (presheafPushforward φ)).app U r = φ.hom.app U r :=
  PresheafOfModules.pushforward_ε_app_apply F (commRingCatHom φ) U r

/-- On sections over `U`, the tensor map of the pushforward of presheaves of modules sends the
pure tensor `m ⊗ₜ n` over `S.obj.obj U` to the same pure tensor over `R.obj.obj (F.op.obj U)`. -/
@[simp]
lemma presheafPushforward_μ_app_tmul (M N : PresheafOfModulesOfCommRing.{u} R.obj)
    (U : Cᵒᵖ) (m : M.obj (F.op.obj U)) (n : N.obj (F.op.obj U)) :
    (Functor.LaxMonoidal.μ (presheafPushforward φ) M N).app U (m ⊗ₜ[S.obj.obj U] n) =
      m ⊗ₜ[R.obj.obj (F.op.obj U)] n :=
  PresheafOfModules.pushforward_μ_app_tmul F (commRingCatHom φ) M N U m n

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The pushforward of sheaves of modules is the sheafification of the pushforward of the
underlying presheaves of modules; the isomorphism is `sheafificationIso` on components. -/
def presheafPushforwardSheafificationIso :
    _root_.SheafOfModules.forget (ringCatSheaf R) ⋙ presheafPushforward φ ⋙
        PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf S).obj) ≅
      _root_.SheafOfModules.pushforward φ :=
  NatIso.ofComponents (fun M ↦ sheafificationIso _ ((_root_.SheafOfModules.pushforward φ).obj M))
    (fun f ↦ sheafificationIso_hom_naturality ((_root_.SheafOfModules.pushforward φ).map f))

/-- The components of `presheafPushforwardSheafificationIso` are `sheafificationIso`. -/
@[simp]
lemma presheafPushforwardSheafificationIso_hom_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (presheafPushforwardSheafificationIso φ).hom.app M =
      (sheafificationIso _ ((_root_.SheafOfModules.pushforward φ).obj M)).hom :=
  (rfl)

/-- The inverse components of `presheafPushforwardSheafificationIso` are `sheafificationIso`. -/
@[simp]
lemma presheafPushforwardSheafificationIso_inv_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (presheafPushforwardSheafificationIso φ).inv.app M =
      (sheafificationIso _ ((_root_.SheafOfModules.pushforward φ).obj M)).inv :=
  (rfl)

variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The pushforward of sheaves of modules is lax monoidal. Its unit map is
`SheafOfModules.unitToPushforwardObjUnit φ` (`SheafOfModules.pushforward_ε`), and its tensor map
is the sheafification of the sectionwise tensor map of the pushforward of presheaves of modules
(`SheafOfModules.pushforward_μ`). -/
instance pushforwardLaxMonoidal : (_root_.SheafOfModules.pushforward φ).LaxMonoidal :=
  Functor.LaxMonoidal.transport (presheafPushforwardSheafificationIso φ)

/-- The unit map of the pushforward of sheaves of modules is Mathlib's
`SheafOfModules.unitToPushforwardObjUnit φ`, given by `φ` on sections. -/
@[simp]
lemma pushforward_ε : Functor.LaxMonoidal.ε (_root_.SheafOfModules.pushforward φ) =
    _root_.SheafOfModules.unitToPushforwardObjUnit φ := by
  have h₁ : Functor.LaxMonoidal.ε (presheafPushforward φ) =
      (_root_.SheafOfModules.unitToPushforwardObjUnit φ).val := by
    ext U : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact presheafPushforward_ε_app_apply φ U
  -- The unit of `forget` is the identity, which `h₂` removes without rewriting inside the
  -- composite, whose source is `𝟙_` only up to unfolding `SheafOfModules.unit`.
  have h₂ : (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf S).obj)).map
      (Functor.LaxMonoidal.ε (presheafPushforward φ) ≫ (presheafPushforward φ).map
        (Functor.LaxMonoidal.ε (_root_.SheafOfModules.forget (ringCatSheaf R)))) =
      (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf S).obj)).map
        (_root_.SheafOfModules.unitToPushforwardObjUnit φ).val :=
    congrArg _ ((congrArg (fun g ↦ _ ≫ (presheafPushforward φ).map g) (forget_ε R)).trans
      ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
        ((Category.comp_id _).trans h₁)))
  rw [pushforwardLaxMonoidal, Functor.LaxMonoidal.transport_ε, Functor.LaxMonoidal.comp_ε,
    Functor.LaxMonoidal.comp_ε, Functor.comp_map, assoc, assoc, ← Functor.map_comp_assoc, h₂,
    sheafification_ε, presheafPushforwardSheafificationIso_hom_app, Iso.inv_comp_eq,
    sheafificationUnitIso_hom, ← sheafificationIso_hom]
  exact sheafificationIso_hom_naturality (_root_.SheafOfModules.unitToPushforwardObjUnit φ)

/-- The tensor map of the pushforward of sheaves of modules: through `tensorUnderlyingIso`, it is
the sheafification of the sectionwise tensor map of the pushforward of presheaves of modules,
followed by the pushforward of the tensor map of `SheafOfModules.forget`. -/
lemma pushforward_μ (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ) M N =
      (((_root_.SheafOfModules.pushforward φ).obj M).tensorUnderlyingIso
          ((_root_.SheafOfModules.pushforward φ).obj N)).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf S).obj)).map
          (Functor.LaxMonoidal.μ (presheafPushforward φ) M.val N.val ≫
            (presheafPushforward φ).map
              (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N)) ≫
        (sheafificationIso _ ((_root_.SheafOfModules.pushforward φ).obj (M ⊗ N))).hom := by
  rw [pushforwardLaxMonoidal, Functor.LaxMonoidal.transport_μ, Functor.LaxMonoidal.comp_μ,
    Functor.LaxMonoidal.comp_μ, Functor.comp_map, assoc, assoc, ← Functor.map_comp_assoc,
    SheafOfModules.tensorUnderlyingIso_hom, assoc]
  -- The two sides differ by `presheafPushforwardSheafificationIso_hom_app` and
  -- `presheafPushforwardSheafificationIso_inv_app`, which `rw` cannot apply here: the objects
  -- `(forget _).obj M` and `M.val` of the composite agree only after unfolding `forget`.
  rfl

variable [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- The pullback of sheaves of modules is oplax monoidal, as the left adjoint of the lax monoidal
pushforward. Its unit map is `SheafOfModules.pullbackObjUnitToUnit φ`
(`SheafOfModules.pullback_η`). -/
instance pullbackOplaxMonoidal : (_root_.SheafOfModules.pullback.{u} φ).OplaxMonoidal :=
  (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal

/-- The pullback--pushforward adjunction is compatible with the oplax monoidal structure of the
pullback and the lax monoidal structure of the pushforward. -/
instance isMonoidal_pullbackPushforwardAdjunction :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).IsMonoidal :=
  inferInstanceAs (letI := (_root_.SheafOfModules.pullbackPushforwardAdjunction φ)
    |>.leftAdjointOplaxMonoidal
    (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).IsMonoidal)

/-- The unit map of the pullback of sheaves of modules is Mathlib's
`SheafOfModules.pullbackObjUnitToUnit φ`. -/
@[simp]
lemma pullback_η : Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ) =
    _root_.SheafOfModules.pullbackObjUnitToUnit φ := by
  rw [pullbackOplaxMonoidal, Adjunction.leftAdjointOplaxMonoidal_η, pushforward_ε]
  exact _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit φ

end SheafOfModules

end

end TauCeti
