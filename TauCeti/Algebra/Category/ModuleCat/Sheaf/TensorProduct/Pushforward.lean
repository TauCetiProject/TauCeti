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
# Pushforward of sheaves of modules is lax symmetric monoidal

Let `F : C ⥤ D` be a continuous functor between small sites, `R` and `S` sheaves of commutative
rings on `D` and `C`, and `φ : S ⟶ F_* R` a morphism of the underlying sheaves of rings. This file
equips the pushforward `SheafOfModules.pushforward φ` of sheaves of modules with its canonical lax
monoidal structure, whose tensor map `φ_* M ⊗ φ_* N ⟶ φ_* (M ⊗ N)` is induced by the sectionwise
map `m ⊗ n ↦ m ⊗ n`, and whose unit map is Mathlib's `SheafOfModules.unitToPushforwardObjUnit φ`.
Consequently the pullback functor, the left adjoint of the pushforward, is oplax monoidal: it
carries comparison maps `φ^* (M ⊗ N) ⟶ φ^* M ⊗ φ^* N` and `φ^* S ⟶ R`, the latter being
Mathlib's `SheafOfModules.pullbackObjUnitToUnit φ`. The pushforward tensor map respects symmetry
(`SheafOfModules.pushforwardLaxBraided`), and so does the pullback tensor comparison
(`SheafOfModules.pullback_map_braiding_hom_comp_δ`), without requiring its invertibility.

The construction proceeds in three steps.

* The inclusion `SheafOfModules.forget` of sheaves of modules into presheaves of modules is right
  adjoint to sheafification, which is monoidal; so the inclusion is lax monoidal
  (`SheafOfModules.forgetLaxMonoidal`, in `Sheaf/TensorProduct/Monoidal.lean`), its tensor map
  being the unit of sheafification `M.val ⊗ N.val ⟶ (M ⊗ N).val`.
* The pushforward of sheaves of modules is isomorphic to the composite of the inclusion, the
  pushforward of presheaves of modules, and sheafification
  (`SheafOfModules.presheafPushforwardSheafificationIso`). All three are lax monoidal, the middle
  one sectionwise (`TauCeti.PresheafOfModules.pushforwardLaxMonoidal`), and the lax monoidal
  structure transports along the isomorphism (`CategoryTheory.Functor.LaxMonoidal.transport`).
* The left adjoint of a lax monoidal functor is oplax monoidal
  (`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`).

The tensor map of the pushforward is characterized on underlying presheaves
(`SheafOfModules.forget_μ_comp_map_pushforward_μ`), since a morphism out of a tensor product of
sheaves of modules is determined by its restriction to the sectionwise tensor product
(`SheafOfModules.tensor_hom_ext`). From this characterization, the identification
`SheafOfModules.pushforwardComp φ ψ` of the composite of two pushforwards with the pushforward
along the composite is a monoidal natural isomorphism. Its conjugate, the composition isomorphism
`SheafOfModules.pullbackComp φ ψ` of pullbacks, is then compatible with the oplax monoidal
structures (`SheafOfModules.pullback_comp_η` and `SheafOfModules.pullback_comp_δ`): the comparison
maps of the pullback along a composite are the composites of the comparison maps.

## Main declarations

* `SheafOfModules.presheafPushforward`: the pushforward of presheaves of modules underlying the
  pushforward of sheaves of modules, with its lax symmetric monoidal structure;
* `SheafOfModules.pushforwardLaxMonoidal` and `SheafOfModules.pushforwardLaxBraided`, with
  `SheafOfModules.pushforward_ε` and `SheafOfModules.pushforward_μ`;
* `SheafOfModules.pullbackOplaxMonoidal`, with `SheafOfModules.pullback_η` and
  `SheafOfModules.pullback_δ`;
* `SheafOfModules.forget_μ_comp_map_pushforward_μ`: the tensor map of the pushforward on underlying
  presheaves;
* `SheafOfModules.isMonoidal_pushforwardComp_hom`: composing pushforwards is compatible with their
  lax monoidal structures;
* `SheafOfModules.pullback_comp_η` and `SheafOfModules.pullback_comp_δ`: composing pullbacks is
  compatible with their oplax monoidal structures.

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

/-- The sectionwise tensor map of pushforward of presheaves of modules respects symmetry. -/
-- As for `presheafPushforwardLaxMonoidal`, keep the body using `commRingCatHom` unexported.
@[instance_reducible]
def presheafPushforwardLaxBraided : (presheafPushforward φ).LaxBraided where
  toLaxMonoidal := presheafPushforwardLaxMonoidal φ
  braided M N :=
    (PresheafOfModules.pushforwardLaxBraided F (commRingCatHom φ)).braided M N

attribute [instance] presheafPushforwardLaxBraided

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

/-- The braiding on the underlying presheaves of pushforward sheaves is the braiding on the
pushforwards of their underlying presheaves. -/
@[simp]
private lemma braiding_hom_forget_pushforward_obj (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (β_ ((_root_.SheafOfModules.forget (ringCatSheaf S)).obj
        ((_root_.SheafOfModules.pushforward φ).obj M))
      ((_root_.SheafOfModules.forget (ringCatSheaf S)).obj
        ((_root_.SheafOfModules.pushforward φ).obj N))).hom =
      (β_ ((presheafPushforward φ).obj M.val) ((presheafPushforward φ).obj N.val)).hom :=
  (rfl)

/-- On underlying presheaves of modules, the pushforward of a morphism of sheaves of modules is
the pushforward of the underlying morphism of presheaves. -/
lemma forget_map_pushforward_map {M N : SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) :
    (_root_.SheafOfModules.forget (ringCatSheaf S)).map
        ((_root_.SheafOfModules.pushforward φ).map f) =
      (presheafPushforward φ).map ((_root_.SheafOfModules.forget (ringCatSheaf R)).map f) :=
  (rfl)

section Comp

variable {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
  [L.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  {G : D ⥤ E} [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L] {T : Sheaf L CommRingCat.{u}}
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj (ringCatSheaf T))

/-- Pushing forward presheaves of modules along `ψ` and then along `φ` is pushing forward along
the composite. -/
lemma presheafPushforward_map_map {A B : PresheafOfModules.{u} (ringCatSheaf T).obj}
    (f : A ⟶ B) :
    (presheafPushforward φ).map ((presheafPushforward ψ).map f) =
      (presheafPushforward (F := F ⋙ G) (R := T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).map f :=
  (rfl)

/-- The tensor map of the composite of two pushforwards of presheaves of modules is the tensor
map of the pushforward along the composite: both send `m ⊗ n` to `m ⊗ n` on sections. -/
@[reassoc]
lemma presheafPushforward_μ_comp (A B : PresheafOfModules.{u} (ringCatSheaf T).obj) :
    Functor.LaxMonoidal.μ (presheafPushforward φ) ((presheafPushforward ψ).obj A)
        ((presheafPushforward ψ).obj B) ≫
      (presheafPushforward φ).map (Functor.LaxMonoidal.μ (presheafPushforward ψ) A B) =
    Functor.LaxMonoidal.μ (presheafPushforward (F := F ⋙ G) (R := T)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) A B := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  have h₁ := presheafPushforward_μ_app_tmul φ ((presheafPushforward ψ).obj A)
    ((presheafPushforward ψ).obj B) U m n
  have h₂ := presheafPushforward_μ_app_tmul ψ A B (F.op.obj U) m n
  have h₃ := presheafPushforward_μ_app_tmul (F := F ⋙ G) (R := T)
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) A B U m n
  exact (congrArg (fun x ↦ ((presheafPushforward φ).map
    (Functor.LaxMonoidal.μ (presheafPushforward ψ) A B)).app U x) h₁).trans (h₂.trans h₃.symm)

omit [(F ⋙ G).IsContinuous J L] in
/-- The components of the composition isomorphism of pushforwards are identities on underlying
presheaves of modules. -/
private lemma forget_map_pushforwardComp_hom_app (M : SheafOfModules.{u} (ringCatSheaf T)) :
    (_root_.SheafOfModules.forget (ringCatSheaf S)).map
      ((_root_.SheafOfModules.pushforwardComp φ ψ).hom.app M) = 𝟙 _ :=
  (rfl)

end Comp

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

/-- The tensor map of the pushforward of sheaves of modules, read on underlying presheaves along
the tensor map of `forget`, is the sectionwise tensor map of the pushforward of presheaves of
modules followed by the pushforward of the tensor map of `forget`. Together with
`SheafOfModules.tensor_hom_ext`, this characterizes `Functor.LaxMonoidal.μ (pushforward φ)`. -/
@[reassoc]
lemma forget_μ_comp_map_pushforward_μ (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf S))
        ((_root_.SheafOfModules.pushforward φ).obj M)
        ((_root_.SheafOfModules.pushforward φ).obj N) ≫
      (_root_.SheafOfModules.forget (ringCatSheaf S)).map
        (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ) M N) =
      Functor.LaxMonoidal.μ (presheafPushforward φ) M.val N.val ≫
        (presheafPushforward φ).map
          (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N) := by
  rw [pushforward_μ, forget_μ_comp_map, Iso.inv_hom_id_assoc,
    ← sheafificationForgetAdjunction_counit_app]
  exact (congrArg _ ((sheafificationForgetAdjunction S).homEquiv_counit _ _ _).symm).trans
    (Equiv.apply_symm_apply _ _)

/-- On pure tensors of sections, the tensor map of sheaf pushforward is the inclusion of
the corresponding pure tensor on the source site into the sheaf tensor product. -/
lemma pushforward_μ_app_tmul (M N : SheafOfModules.{u} (ringCatSheaf R)) (U : Cᵒᵖ)
    (m : M.val.obj (F.op.obj U)) (n : N.val.obj (F.op.obj U)) :
    (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ) M N).val.app U
      ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf S))
        ((_root_.SheafOfModules.pushforward φ).obj M)
        ((_root_.SheafOfModules.pushforward φ).obj N)).app U (m ⊗ₜ[S.obj.obj U] n)) =
    (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
      (F.op.obj U) (m ⊗ₜ[R.obj.obj (F.op.obj U)] n) := by
  have h := congrArg (fun p ↦ (p.app U).hom (m ⊗ₜ[S.obj.obj U] n))
    (forget_μ_comp_map_pushforward_μ φ M N)
  -- Evaluate the presheaf composites as functions; their restriction-of-scalars wrappers
  -- prevent rewriting the bundled module compositions directly.
  change (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ) M N).val.app U
      ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf S))
        ((_root_.SheafOfModules.pushforward φ).obj M)
        ((_root_.SheafOfModules.pushforward φ).obj N)).app U (m ⊗ₜ[S.obj.obj U] n)) =
    (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
      (F.op.obj U)
      ((Functor.LaxMonoidal.μ (presheafPushforward φ) M.val N.val).app U
        (m ⊗ₜ[S.obj.obj U] n)) at h
  exact h.trans (congrArg
    ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
      (F.op.obj U)) (presheafPushforward_μ_app_tmul φ M.val N.val U m n))

/-- Pushforward of sheaves of modules respects symmetry: its lax tensor map commutes with
interchanging the factors. -/
instance pushforwardLaxBraided : (_root_.SheafOfModules.pushforward φ).LaxBraided where
  toLaxMonoidal := pushforwardLaxMonoidal φ
  braided M N := by
    apply tensor_hom_ext
    simp only [Functor.map_comp]
    rw [forget_μ_comp_map_pushforward_μ_assoc]
    -- The sectionwise characterization writes the objects as `M.val` rather than
    -- `(forget _).obj M`; `erw` unfolds this wrapper when applying the braiding laws.
    erw [Functor.LaxBraided.braided_assoc]
    rw [forget_μ_comp_map_pushforward_μ, forget_map_pushforward_map]
    erw [Category.assoc, ← Functor.map_comp]
    erw [Functor.LaxBraided.braided]
    erw [Functor.map_comp, Functor.LaxBraided.braided_assoc]
    exact congrArg
      (· ≫ Functor.LaxMonoidal.μ (presheafPushforward φ) N.val M.val ≫
        (presheafPushforward φ).map
          (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) N M))
      (braiding_hom_forget_pushforward_obj φ M N).symm

section Comp

variable {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
  [L.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {G : D ⥤ E} [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L] {T : Sheaf L CommRingCat.{u}}
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj (ringCatSheaf T))

/-- The identification of the composite of two pushforwards of sheaves of modules with the
pushforward along the composite is a monoidal natural transformation. -/
instance isMonoidal_pushforwardComp_hom :
    NatTrans.IsMonoidal (_root_.SheafOfModules.pushforwardComp φ ψ).hom where
  unit := by
    rw [Functor.LaxMonoidal.comp_ε, pushforward_ε, pushforward_ε, pushforward_ε]
    -- On each object, `pushforwardComp` is the identity and the unit map along the composite is
    -- the composite of the unit maps.
    ext U : 3
    rfl
  tensor M N := by
    apply tensor_hom_ext
    simp only [Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc, Functor.comp_obj,
      Functor.LaxMonoidal.comp_μ, forget_μ_comp_map_pushforward_μ_assoc,
      forget_μ_comp_map_pushforward_μ, assoc, forget_map_pushforward_map]
    have e : (presheafPushforward φ).map (Functor.LaxMonoidal.μ
          (_root_.SheafOfModules.forget (ringCatSheaf R))
            ((_root_.SheafOfModules.pushforward ψ).obj M)
            ((_root_.SheafOfModules.pushforward ψ).obj N)) ≫
        (presheafPushforward φ).map ((_root_.SheafOfModules.forget (ringCatSheaf R)).map
          (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward ψ) M N)) =
        (presheafPushforward φ).map (Functor.LaxMonoidal.μ (presheafPushforward ψ) M.val N.val) ≫
          (presheafPushforward φ).map ((presheafPushforward ψ).map
            (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf T)) M N)) := by
      rw [← Functor.map_comp, ← Functor.map_comp, forget_μ_comp_map_pushforward_μ]
      -- The two sides differ only in how the objects `(forget _).obj M` and `M.val` are written.
      rfl
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (fun x ↦ _ ≫ x ≫ _) e).trans ?_
    simp only [forget_map_pushforwardComp_hom_app]
    -- The identities `forget_map_pushforwardComp_hom_app` are between objects that agree only up
    -- to unfolding the pushforward along the composite, so the unit laws are applied with `erw`.
    erw [comp_id, tensorHom_id, id_whiskerRight, id_comp, presheafPushforward_μ_comp_assoc,
      presheafPushforward_map_map]
    -- The two sides now differ only in whether the objects are written through the composite of
    -- the pushforwards or through the pushforward along the composite.
    rfl

end Comp

variable [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- The pullback of sheaves of modules is oplax monoidal, as the left adjoint of the lax monoidal
pushforward. Its unit map is `SheafOfModules.pullbackObjUnitToUnit φ`
(`SheafOfModules.pullback_η`), and its tensor map is the mate of the tensor map of the pushforward
(`SheafOfModules.pullback_δ`). -/
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

/-- The tensor map `φ^* (M ⊗ N) ⟶ φ^* M ⊗ φ^* N` of the pullback of sheaves of modules is the
mate, under the pullback--pushforward adjunction, of the composite of the units
`M ⟶ φ_* φ^* M` and `N ⟶ φ_* φ^* N` with the tensor map `φ_* φ^* M ⊗ φ_* φ^* N ⟶
φ_* (φ^* M ⊗ φ^* N)` of the pushforward. -/
lemma pullback_δ (M N : SheafOfModules.{u} (ringCatSheaf S)) :
    Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) M N =
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _).symm
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M ⊗ₘ
            (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app N) ≫
          Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ) _ _) :=
  Adjunction.leftAdjointOplaxMonoidal_δ _ _ _

/-- The canonical tensor comparison of pullback commutes with interchanging the factors.
This statement does not require that the comparison be invertible. -/
@[reassoc]
lemma pullback_map_braiding_hom_comp_δ (M N : SheafOfModules.{u} (ringCatSheaf S)) :
    (_root_.SheafOfModules.pullback φ).map (β_ M N).hom ≫
        Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) N M =
      Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N ≫
        (β_ ((_root_.SheafOfModules.pullback φ).obj M)
          ((_root_.SheafOfModules.pullback φ).obj N)).hom :=
  (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).map_braiding_hom_comp_δ M N

section Comp

variable {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
  [L.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify L AddCommGrpCat.{u}] [L.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {G : D ⥤ E} [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L] {T : Sheaf L CommRingCat.{u}}
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj (ringCatSheaf T))
  [(_root_.SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]

/-- The unit map of the pullback along a composite is the composite of the unit maps of the two
pullbacks, through the composition isomorphism `SheafOfModules.pullbackComp`. -/
lemma pullback_comp_η :
    Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G)
        (R := ringCatSheaf T) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) =
      (_root_.SheafOfModules.pullbackComp φ ψ).inv.app (𝟙_ _) ≫
        (_root_.SheafOfModules.pullback ψ).map
          (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback φ)) ≫
        Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback ψ) := by
  have h := Adjunction.app_tensorUnit_comp_η_of_conjugateEquiv
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).comp
      (_root_.SheafOfModules.pullbackPushforwardAdjunction ψ))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction _)
    (_root_.SheafOfModules.conjugateEquiv_pullbackComp_inv φ ψ)
  rw [Functor.OplaxMonoidal.comp_η] at h
  exact h.symm

/-- The tensor map of the pullback along a composite is the composite of the tensor maps of the
two pullbacks, through the composition isomorphism `SheafOfModules.pullbackComp`. Together with
`SheafOfModules.pullback_comp_η`, this says that the composition isomorphism of pullbacks is an
isomorphism of oplax monoidal functors. -/
lemma pullback_comp_δ (M N : SheafOfModules.{u} (ringCatSheaf S)) :
    Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} (F := F ⋙ G) (R := ringCatSheaf T)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)) M N =
      (_root_.SheafOfModules.pullbackComp φ ψ).inv.app (M ⊗ N) ≫
        (_root_.SheafOfModules.pullback ψ).map
          (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N) ≫
        Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback ψ) _ _ ≫
        ((_root_.SheafOfModules.pullbackComp φ ψ).hom.app M ⊗ₘ
          (_root_.SheafOfModules.pullbackComp φ ψ).hom.app N) := by
  have h := Adjunction.app_tensor_comp_δ_of_conjugateEquiv
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).comp
      (_root_.SheafOfModules.pullbackPushforwardAdjunction ψ))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction _)
    (_root_.SheafOfModules.conjugateEquiv_pullbackComp_inv φ ψ) M N
  rw [Functor.OplaxMonoidal.comp_δ] at h
  simpa using ((Iso.comp_inv_eq ((_root_.SheafOfModules.pullbackComp φ ψ).app M ⊗ᵢ
    (_root_.SheafOfModules.pullbackComp φ ψ).app N)).mp h.symm)

end Comp

end SheafOfModules

end

end TauCeti
