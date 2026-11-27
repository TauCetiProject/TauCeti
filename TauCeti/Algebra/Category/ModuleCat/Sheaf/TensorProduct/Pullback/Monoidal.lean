/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Stalk
import Mathlib.CategoryTheory.Limits.Final

/-!
# Strong symmetric monoidal pullback of sheaves of modules

For every morphism of ringed spaces `(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)` and all sheaves of
`𝒪_X`-modules `E` and `F`, the canonical oplax tensor comparison
`δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` of `SheafOfModules.pullbackOplaxMonoidal` is an
isomorphism (`TauCeti.SheafOfModules.isIso_pullback_δ`), with no flatness, finiteness, or
quasi-coherence hypothesis on `E` or `F` (Stacks Project, Tag 01CD).

On stalks at `y : Y`, the stalk equivalences `TauCeti.SheafOfModules.pullbackStalkEquiv` and
`TauCeti.SheafOfModules.tensorObjStalkEquiv` identify the stalk map of `δ` with the base-change
distributivity isomorphism
`𝒪_{Y,y} ⊗ (E_{f(y)} ⊗ F_{f(y)}) ≃ (𝒪_{Y,y} ⊗ E_{f(y)}) ⊗ (𝒪_{Y,y} ⊗ F_{f(y)})`
(`TauCeti.SheafOfModules.stalkMapCommRing_pullback_δ`). Since stalks detect isomorphisms of sheaves
of modules (`SheafOfModules.isIso_iff_forall_bijective_stalkMapCommRing`), `δ` is invertible.

Since the unit comparison `η : f^* 𝒪_X ⟶ 𝒪_Y` (`SheafOfModules.pullbackObjUnitToUnit`) is also an
isomorphism (`Opens.map f` being final), `SheafOfModules.pullback φ` inherits a strong symmetric
monoidal structure (`TauCeti.SheafOfModules.pullbackMonoidal` and
`TauCeti.SheafOfModules.pullbackBraided`), whose tensor and unit maps invert `δ` and `η`. Mathlib's
composition isomorphism `SheafOfModules.pullbackComp` respects this monoidal structure
(`TauCeti.SheafOfModules.isMonoidal_pullbackComp_hom`). (The corresponding identity coherence is in
`TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Identity`.)

## Main declarations

* `TauCeti.SheafOfModules.pullbackTensorStalkEquiv` and
  `TauCeti.SheafOfModules.pullbackTensorStalkEquiv_germ`: the stalk equivalence
  `(f^* (E ⊗ F))_y ≃ (f^* E ⊗ f^* F)_y` and its value on pullback-unit pure-tensor germs;
* `TauCeti.SheafOfModules.stalkMapCommRing_pullback_δ`: on stalks at `y`, the tensor comparison `δ`
  of pullback is the base-change distributivity equivalence;
* `TauCeti.SheafOfModules.isIso_pullback_δ` and `TauCeti.SheafOfModules.isIso_pullback_η`:
  invertibility of the oplax tensor and unit comparisons of module pullback;
* `TauCeti.SheafOfModules.pullbackMonoidal` and `TauCeti.SheafOfModules.pullbackBraided`:
  strong symmetric monoidal structure on module pullback along a morphism of ringed spaces, with
  `pullback_μ` and `pullback_ε`;
* `TauCeti.SheafOfModules.pullbackCompMonoidal` and
  `TauCeti.SheafOfModules.isMonoidal_pullbackComp_hom`: monoidal structure on a composite pullback
  and monoidality of `pullbackComp`, with `pullback_comp_ε` and `pullback_comp_μ`.

## References

* The Stacks Project, *Sheaves of Modules*, Tag 01CD (pullback of tensor products).
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

section RingedSpace

variable {X Y : TopCat.{u}}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- On sections over `U`, the oplax tensor comparison `δ (pullback φ) E F` carries the unit image
of the sectionwise pure tensor `e ⊗ₜ g` to the sectionwise pure tensor of the unit images of `e`
and `g`. -/
private lemma pullback_δ_app_pullbackUnitApp_forget_μ
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (U : Opens X)
    (e : E.val.obj (op U)) (g : F.val.obj (op U)) :
    ((Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F).val.app
        (op ((Opens.map f).obj U)))
      (pullbackUnitApp φ (E ⊗ F) U
        (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app
          (op U)).hom (e ⊗ₜ[𝒪X.obj.obj (op U)] g))) =
    ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪Y))
        ((_root_.SheafOfModules.pullback.{u} φ).obj E)
        ((_root_.SheafOfModules.pullback.{u} φ).obj F)).app (op ((Opens.map f).obj U))).hom
      (pullbackUnitApp φ E U e ⊗ₜ[𝒪Y.obj.obj (op ((Opens.map f).obj U))]
        pullbackUnitApp φ F U g) := by
  let adj := _root_.SheafOfModules.pullbackPushforwardAdjunction.{u} φ
  -- The adjunction relation `η_{E ⊗ F} ≫ f_* δ_{E,F} = (η_E ⊗ₘ η_F) ≫ μ_{f_*}` evaluates on
  -- pure tensors through naturality of `forget_μ` and `pushforward_μ_app_tmul`.
  have hadj := congrArg (fun p ↦ (p.val.app (op U)).hom
      (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app
        (op U)).hom (e ⊗ₜ[𝒪X.obj.obj (op U)] g)))
    (adj.unit_app_tensor_comp_map_δ E F)
  have hnat := congrArg (fun p ↦ (p.app (op U)).hom (e ⊗ₜ[𝒪X.obj.obj (op U)] g))
    (Functor.LaxMonoidal.μ_natural (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X))
      (adj.unit.app E) (adj.unit.app F)).symm
  have hpush := _root_.SheafOfModules.pushforward_μ_app_tmul φ
    ((_root_.SheafOfModules.pullback.{u} φ).obj E)
    ((_root_.SheafOfModules.pullback.{u} φ).obj F) (op U)
    (pullbackUnitApp φ E U e) (pullbackUnitApp φ F U g)
  dsimp only [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.comp_apply] at hadj hnat hpush
  exact hadj.trans ((congrArg ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ)
    ((_root_.SheafOfModules.pullback.{u} φ).obj E)
    ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.app (op U)) hnat).trans hpush)

/-- The canonical `𝒪_{Y,y}`-linear equivalence `(f^* (E ⊗ F))_y ≃ (f^* E ⊗ f^* F)_y` induced by
`pullbackStalkEquiv`, `tensorObjStalkEquiv`, and `AlgebraTensorModule.distribBaseChange`. -/
def pullbackTensorStalkEquiv (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y) :
    ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)).val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        ↑(TopCat.Presheaf.stalk
          (((_root_.SheafOfModules.pullback.{u} φ).obj E) ⊗
            ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.presheaf y) :=
  letI := stalkAlgebra φ y
  (pullbackStalkEquiv φ (E ⊗ F) y).symm.trans <|
    ((tensorObjStalkEquiv 𝒪X E F (f y)).baseChange
        ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
        ↑(TopCat.Presheaf.stalk (E ⊗ F).val.presheaf (f y))
        (↑(TopCat.Presheaf.stalk E.val.presheaf (f y)) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
          ↑(TopCat.Presheaf.stalk F.val.presheaf (f y)))).trans <|
      (TensorProduct.AlgebraTensorModule.distribBaseChange
          ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
          ↑(TopCat.Presheaf.stalk E.val.presheaf (f y))
          ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))).trans <|
        (TensorProduct.congr (pullbackStalkEquiv φ E y) (pullbackStalkEquiv φ F y)).trans
          (tensorObjStalkEquiv 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
            ((_root_.SheafOfModules.pullback.{u} φ).obj F) y).symm

/-- Action of `pullbackTensorStalkEquiv` on an element transported along `pullbackStalkEquiv` and
`tensorObjStalkEquiv`. -/
theorem pullbackTensorStalkEquiv_tmul_symm_tmul
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y)
    (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y))
    (s : ↑(TopCat.Presheaf.stalk E.val.presheaf (f y)))
    (t : ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))) :
    letI := stalkAlgebra φ y
    pullbackTensorStalkEquiv φ E F y
        (pullbackStalkEquiv φ (E ⊗ F) y
          (a ⊗ₜ ((tensorObjStalkEquiv 𝒪X E F (f y)).symm (s ⊗ₜ t)))) =
      (tensorObjStalkEquiv 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
        ((_root_.SheafOfModules.pullback.{u} φ).obj F) y).symm
        (pullbackStalkEquiv φ E y (a ⊗ₜ s) ⊗ₜ pullbackStalkEquiv φ F y (1 ⊗ₜ t)) := by
  let := stalkAlgebra φ y
  unfold pullbackTensorStalkEquiv
  -- `pullbackStalkEquiv` uses `pullbackStalkModule` while `tensorObjStalkEquiv` uses
  -- `SheafOfModules.stalkModule`, which agree definitionally after unfolding `ringCatSheaf`.
  erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.apply_symm_apply, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.congr_tmul]
  rfl

/-- On the germ of the pullback-unit image of a sectionwise pure tensor `e ⊗ₜ g`,
`pullbackTensorStalkEquiv` returns the germ of the sectionwise pure tensor of the pullback-unit
images of `e` and `g`. -/
@[simp]
theorem pullbackTensorStalkEquiv_germ
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y)
    (V : Opens X) (hyV : f y ∈ V) (e : E.val.obj (op V)) (g : F.val.obj (op V)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, sheafCompose_obj_obj,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (pullbackTensorStalkEquiv φ E F y
        (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)).val.presheaf
          ((Opens.map f).obj V) y hyV
          (pullbackUnitApp φ (E ⊗ F) V
            (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app
              (op V)).hom (e ⊗ₜ[𝒪X.obj.obj (op V)] g)))) =
      TopCat.Presheaf.germ
        (((_root_.SheafOfModules.pullback.{u} φ).obj E) ⊗
          ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.presheaf
        ((Opens.map f).obj V) y hyV
        (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪Y))
            ((_root_.SheafOfModules.pullback.{u} φ).obj E)
            ((_root_.SheafOfModules.pullback.{u} φ).obj F)).app
            (op ((Opens.map f).obj V))).hom
          (pullbackUnitApp φ E V e ⊗ₜ[𝒪Y.obj.obj (op ((Opens.map f).obj V))]
            pullbackUnitApp φ F V g))) := by
  let := stalkAlgebra φ y
  -- Identify the germs with `pullbackStalkEquiv` and `tensorObjStalkEquiv` on pure tensors;
  -- `erw` unfolds `ringCatSheaf` between `SheafOfModules` and `PresheafOfModules` germ lemmas.
  have hlhs :
      TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)).val.presheaf
          ((Opens.map f).obj V) y hyV
          (pullbackUnitApp φ (E ⊗ F) V
            (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app
              (op V)).hom (e ⊗ₜ[𝒪X.obj.obj (op V)] g))) =
        pullbackStalkEquiv φ (E ⊗ F) y
          (1 ⊗ₜ ((tensorObjStalkEquiv 𝒪X E F (f y)).symm
            (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV e ⊗ₜ
              TopCat.Presheaf.germ F.val.presheaf V (f y) hyV g))) := by
    erw [tensorObjStalkEquiv_symm_tmul_germ 𝒪X E F (f y) V hyV e g,
      pullbackStalkEquiv_tmul_germ φ (E ⊗ F) y 1 V hyV, one_smul]
    rfl
  refine (congrArg (pullbackTensorStalkEquiv φ E F y) hlhs).trans
    ((pullbackTensorStalkEquiv_tmul_symm_tmul φ E F y 1 _ _).trans ?_)
  erw [(pullbackStalkEquiv_tmul_germ φ E y 1 V hyV e).trans (one_smul _ _),
    (pullbackStalkEquiv_tmul_germ φ F y 1 V hyV g).trans (one_smul _ _),
    tensorObjStalkEquiv_symm_tmul_germ 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
      ((_root_.SheafOfModules.pullback.{u} φ).obj F) y ((Opens.map f).obj V) hyV
      (pullbackUnitApp φ E V e) (pullbackUnitApp φ F V g)]

private lemma stalkMapCommRing_pullback_δ_tmul_germ
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y)
    (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (V : Opens X) (hyV : f y ∈ V)
    (e' : E.val.obj (op V)) (g : F.val.obj (op V)) :
    letI := stalkAlgebra φ y
    PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
        (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F).val
        (pullbackStalkEquiv φ (E ⊗ F) y
          (a ⊗ₜ ((tensorObjStalkEquiv 𝒪X E F (f y)).symm
            (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV e' ⊗ₜ
              TopCat.Presheaf.germ F.val.presheaf V (f y) hyV g)))) =
      a • TopCat.Presheaf.germ
        (((_root_.SheafOfModules.pullback.{u} φ).obj E) ⊗
          ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.presheaf
        ((Opens.map f).obj V) y hyV
        (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪Y))
            ((_root_.SheafOfModules.pullback.{u} φ).obj E)
            ((_root_.SheafOfModules.pullback.{u} φ).obj F)).app
            (op ((Opens.map f).obj V))).hom
          (pullbackUnitApp φ E V e' ⊗ₜ[𝒪Y.obj.obj (op ((Opens.map f).obj V))]
            pullbackUnitApp φ F V g)) := by
  let := stalkAlgebra φ y
  -- `erw` unfolds `ringCatSheaf` between `SheafOfModules` and `PresheafOfModules` germ lemmas.
  erw [tensorObjStalkEquiv_symm_tmul_germ 𝒪X E F (f y) V hyV e' g,
    pullbackStalkEquiv_tmul_germ φ (E ⊗ F) y a V hyV, map_smul,
    PresheafOfModules.stalkMapCommRing_germ]
  exact congrArg (fun z ↦ a • TopCat.Presheaf.germ
      (((_root_.SheafOfModules.pullback.{u} φ).obj E) ⊗
        ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.presheaf
      ((Opens.map f).obj V) y hyV z)
    (pullback_δ_app_pullbackUnitApp_forget_μ φ E F V e' g)

/-- On stalks at `y : Y`, the oplax tensor comparison `δ (pullback φ) E F` coincides with the
canonical equivalence `pullbackTensorStalkEquiv` distributing base change over tensor product. -/
theorem stalkMapCommRing_pullback_δ
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y) :
    PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
        (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F).val =
      (pullbackTensorStalkEquiv φ E F y).toLinearMap := by
  let := stalkAlgebra φ y
  apply (LinearMap.cancel_right (pullbackStalkEquiv φ (E ⊗ F) y).surjective).mp
  refine LinearMap.ext fun au ↦ ?_
  induction au using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => rw [map_add, map_add, hx₁, hx₂]
  | tmul a u =>
    obtain ⟨st, rfl⟩ := (tensorObjStalkEquiv 𝒪X E F (f y)).symm.surjective u
    induction st using TensorProduct.inductionOn with
    | add x₁ x₂ hx₁ hx₂ =>
      rw [LinearEquiv.map_add, TensorProduct.tmul_add, map_add, map_add, hx₁, hx₂]
    | tmul s t =>
      obtain ⟨U, hyU, e, rfl⟩ := TopCat.Presheaf.exists_germ_eq E.val.presheaf s
      obtain ⟨V, hVU, hyV, g, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf t hyU
      let e' : E.val.obj (op V) := E.val.map (homOfLE hVU).op e
      have he' : TopCat.Presheaf.germ E.val.presheaf U (f y) hyU e =
          TopCat.Presheaf.germ E.val.presheaf V (f y) hyV e' :=
        (TopCat.Presheaf.germ_res_apply E.val.presheaf (homOfLE hVU) (f y) hyV e).symm
      rw [he']
      -- Simplify only the RHS (`erw` aligns `ringCatSheaf` carriers and `stalkModule` instances).
      conv_rhs =>
        erw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          tensorObjStalkEquiv_symm_tmul_germ 𝒪X E F (f y) V hyV e' g,
          pullbackStalkEquiv_tmul_germ φ (E ⊗ F) y a V hyV, map_smul]
      exact (stalkMapCommRing_pullback_δ_tmul_germ φ E F y a V hyV e' g).trans
        (congrArg (a • ·) (pullbackTensorStalkEquiv_germ φ E F y V hyV e' g)).symm

/-- **Invertibility of the pullback tensor comparison.** For every morphism of ringed spaces
`(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)` and all sheaves of `𝒪_X`-modules `E` and `F`, the canonical oplax
tensor comparison `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` is an isomorphism, without any flatness,
finiteness, or quasi-coherence assumptions (Stacks Project, Tag 01CD). -/
instance isIso_pullback_δ (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) := by
  rw [_root_.SheafOfModules.isIso_iff_forall_bijective_stalkMapCommRing]
  intro y
  rw [stalkMapCommRing_pullback_δ]
  exact (pullbackTensorStalkEquiv φ E F y).bijective

/-- For every morphism of ringed spaces `(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)`, the canonical oplax unit
comparison `η : f^* 𝒪_X ⟶ 𝒪_Y` is an isomorphism. -/
instance isIso_pullback_η :
    IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ)) := by
  rw [_root_.SheafOfModules.pullback_η φ]
  infer_instance

/-- Pullback of sheaves of modules along a morphism of ringed spaces is strong monoidal, with
inverse comparisons inherited from `SheafOfModules.pullbackOplaxMonoidal`. -/
@[expose, instance_reducible]
def pullbackMonoidal : (_root_.SheafOfModules.pullback.{u} φ).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} φ)

attribute [instance] pullbackMonoidal

/-- Pullback of sheaves of modules along a morphism of ringed spaces is strong symmetric
monoidal. -/
@[expose, instance_reducible]
def pullbackBraided : (_root_.SheafOfModules.pullback.{u} φ).Braided :=
  (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).leftAdjointBraided

attribute [instance] pullbackBraided

/-- The strong monoidal tensor map of module pullback inverts the canonical oplax tensor
comparison. -/
theorem pullback_μ (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} φ) E F =
      inv (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) :=
  IsIso.eq_inv_of_hom_inv_id (Functor.Monoidal.δ_μ _ E F)

/-- The strong monoidal unit map of module pullback inverts
`SheafOfModules.pullbackObjUnitToUnit`. -/
theorem pullback_ε :
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ) =
      inv (_root_.SheafOfModules.pullbackObjUnitToUnit φ) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← _root_.SheafOfModules.pullback_η φ]
  exact Functor.Monoidal.η_ε (_root_.SheafOfModules.pullback.{u} φ)

end RingedSpace

section Composition

variable {X Y Z : TopCat.{u}}
  {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  {𝒪Z : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
  {f : Y ⟶ X} {g : Z ⟶ Y}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj (ringCatSheaf 𝒪Y))
  (ψ : ringCatSheaf 𝒪Y ⟶
    ((Opens.map g).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z)).obj (ringCatSheaf 𝒪Z))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]

/-- The unit comparison for a composite pullback of sheaves of modules on ringed spaces is an
isomorphism. -/
instance isIso_pullback_comp_η :
    IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u}
      (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))) := by
  rw [_root_.SheafOfModules.pullback_comp_η φ ψ]
  infer_instance

/-- The tensor comparison for a composite pullback of sheaves of modules on ringed spaces is an
isomorphism. -/
instance isIso_pullback_comp_δ (M N : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u}
      (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) M N) := by
  rw [_root_.SheafOfModules.pullback_comp_δ φ ψ M N]
  infer_instance

/-- The strong monoidal structure on a composite pullback of sheaves of modules on ringed spaces. -/
@[expose, instance_reducible]
def pullbackCompMonoidal :
    (_root_.SheafOfModules.pullback.{u}
      (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

attribute [instance] pullbackCompMonoidal

/-- The canonical composition isomorphism `SheafOfModules.pullbackComp` respects the strong
monoidal structures of module pullbacks along morphisms of ringed spaces. -/
instance isMonoidal_pullbackComp_hom :
    NatTrans.IsMonoidal (_root_.SheafOfModules.pullbackComp φ ψ).hom where
  unit := by
    rw [← cancel_mono (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u}
        (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z)
        (R := ringCatSheaf 𝒪Z) (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))),
      Category.assoc]
    have hη :
        (_root_.SheafOfModules.pullbackComp φ ψ).hom.app (𝟙_ _) ≫
            Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u}
              (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z)
              (R := ringCatSheaf 𝒪Z) (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
                (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) =
          Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ ⋙
            _root_.SheafOfModules.pullback.{u} ψ) := by
      rw [Functor.OplaxMonoidal.comp_η,
        ← cancel_epi ((_root_.SheafOfModules.pullbackComp φ ψ).inv.app (𝟙_ _)),
        Iso.inv_hom_id_app_assoc]
      exact _root_.SheafOfModules.pullback_comp_η φ ψ
    rw [hη]
    exact (Functor.Monoidal.ε_η (_root_.SheafOfModules.pullback.{u} φ ⋙
      _root_.SheafOfModules.pullback.{u} ψ)).trans (Functor.Monoidal.ε_η _).symm
  tensor M N := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ ⋙
        _root_.SheafOfModules.pullback.{u} ψ) M N),
      ← cancel_mono (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u}
        (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z)
        (R := ringCatSheaf 𝒪Z) (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) M N)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    rw [Functor.OplaxMonoidal.comp_δ,
      ← cancel_epi ((_root_.SheafOfModules.pullbackComp φ ψ).inv.app (M ⊗ N)),
      Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc] using _root_.SheafOfModules.pullback_comp_δ φ ψ M N

/-- The strong monoidal unit map of a composite pullback is the composite of the unit maps through
`SheafOfModules.pullbackComp`. -/
@[reassoc]
theorem pullback_comp_ε :
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} ψ) ≫
        (_root_.SheafOfModules.pullback.{u} ψ).map
          (Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ)) ≫
        (_root_.SheafOfModules.pullbackComp φ ψ).hom.app (𝟙_ _) =
      Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u}
        (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
        (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) := by
  have hu := NatTrans.IsMonoidal.unit (τ := (_root_.SheafOfModules.pullbackComp φ ψ).hom)
  rw [Functor.LaxMonoidal.comp_ε, Category.assoc] at hu
  exact hu

/-- The strong monoidal tensor map of a composite pullback is the composite of the tensor maps
through `SheafOfModules.pullbackComp`. -/
@[reassoc]
theorem pullback_comp_μ
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} ψ) _ _ ≫
        (_root_.SheafOfModules.pullback.{u} ψ).map
          (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} φ) M N) ≫
        (_root_.SheafOfModules.pullbackComp φ ψ).hom.app (M ⊗ N) =
      ((_root_.SheafOfModules.pullbackComp φ ψ).hom.app M ⊗ₘ
          (_root_.SheafOfModules.pullbackComp φ ψ).hom.app N) ≫
        Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u}
          (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z)
          (R := ringCatSheaf 𝒪Z)
          (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
            (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) M N := by
  have ht := NatTrans.IsMonoidal.tensor (τ := (_root_.SheafOfModules.pullbackComp φ ψ).hom) M N
  rw [Functor.LaxMonoidal.comp_μ, Category.assoc] at ht
  exact ht

end Composition

end SheafOfModules

end

end TauCeti
