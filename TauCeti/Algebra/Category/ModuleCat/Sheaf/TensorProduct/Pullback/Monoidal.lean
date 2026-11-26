/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Identity
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Stalk
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Topology.Sheaves.Stalks

/-!
# Strong symmetric monoidal pullback of sheaves of modules

For every morphism of ringed spaces `(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)` and all sheaves of
`𝒪_X`-modules `E` and `F`, the canonical oplax tensor comparison
`δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` of `TauCeti.SheafOfModules.pullbackOplaxMonoidal` is an
isomorphism (`TauCeti.SheafOfModules.isIso_pullback_δ`), with no flatness, finiteness, or
quasi-coherence hypothesis on `E` or `F` (Stacks Project, Tag 01CD).

On stalks at `y : Y`, the stalk equivalence `TauCeti.SheafOfModules.pullbackStalkEquiv` and
`TauCeti.SheafOfModules.tensorObjStalkEquiv` identify the stalk map of `δ` with the base-change
distributivity isomorphism
`𝒪_{Y,y} ⊗ (E_{f(y)} ⊗ F_{f(y)}) ≃ (𝒪_{Y,y} ⊗ E_{f(y)}) ⊗ (𝒪_{Y,y} ⊗ F_{f(y)})`
(`TauCeti.SheafOfModules.stalkMapCommRing_pullback_δ`). Since stalks detect isomorphisms of sheaves
of abelian groups (`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`) and `SheafOfModules.toSheaf`
reflects isomorphisms, `δ` is invertible.

Since the unit comparison `η : f^* 𝒪_X ⟶ 𝒪_Y` (`SheafOfModules.pullbackObjUnitToUnit`) is also an
isomorphism (`Opens.map f` being final), `SheafOfModules.pullback φ` inherits a strong symmetric
monoidal structure (`TauCeti.SheafOfModules.pullbackMonoidal` and
`TauCeti.SheafOfModules.pullbackBraided`), whose tensor and unit maps invert `δ` and `η`. Mathlib's
identity and composition isomorphisms `SheafOfModules.pullbackId` and `SheafOfModules.pullbackComp`
respect this monoidal structure (`TauCeti.SheafOfModules.isMonoidal_pullbackId_hom` and
`TauCeti.SheafOfModules.isMonoidal_pullbackComp_hom`).

## Main declarations

* `TauCeti.SheafOfModules.isIso_iff_forall_bijective_stalkMapCommRing`: a morphism of sheaves of
  modules over a sheaf of commutative rings is an isomorphism iff all of its stalk maps are
  bijective;
* `TauCeti.SheafOfModules.tensorObjStalkEquiv`: the stalk of the monoidal tensor product `M ⊗ N` is
  canonically the tensor product of the stalks over the ring stalk;
* `TauCeti.SheafOfModules.stalkMapCommRing_pullback_δ`: on stalks at `y`, the tensor comparison `δ`
  of pullback is the base-change distributivity equivalence;
* `TauCeti.SheafOfModules.isIso_pullback_δ` and `TauCeti.SheafOfModules.isIso_pullback_η`:
  invertibility of the oplax tensor and unit comparisons of module pullback;
* `TauCeti.SheafOfModules.pullbackMonoidal` and `TauCeti.SheafOfModules.pullbackBraided`:
  strong symmetric monoidal structure on module pullback along a morphism of ringed spaces, with
  `pullback_μ` and `pullback_ε`;
* `TauCeti.SheafOfModules.isMonoidal_pullbackId_hom` and
  `TauCeti.SheafOfModules.isMonoidal_pullbackComp_hom`: monoidality of `pullbackId` and
  `pullbackComp`.

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

section Stalk

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- A morphism of sheaves of modules over a sheaf of commutative rings on a topological space
is an isomorphism if and only if all of its stalk maps are bijective. -/
theorem isIso_iff_forall_bijective_stalkMapCommRing
    {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)} (g : M ⟶ N) :
    IsIso g ↔
      ∀ x : X, Function.Bijective (PresheafOfModules.stalkMapCommRing (S := R.obj) x g.val) := by
  rw [← isIso_iff_of_reflects_iso g (_root_.SheafOfModules.toSheaf (ringCatSheaf R)),
    TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  refine forall_congr' fun x ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  -- Compare the `AddCommGrpCat`-stalk map with `stalkMapCommRing`.
  erw [PresheafOfModules.coe_stalkMapCommRing (S := R.obj) x g.val]
  rfl

variable (R)

/-- The stalk of the monoidal tensor product `M ⊗ N` at `x` is canonically the tensor product of
the stalks of `M` and `N` over the ring stalk. -/
def tensorObjStalkEquiv (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) (x : X) :
    ↑(TopCat.Presheaf.stalk (M ⊗ N).val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  (PresheafOfModules.stalkLinearEquivCommRing (S := R.obj) x
    ((_root_.SheafOfModules.forget _).mapIso (M.tensorUnderlyingIso N ≪≫
      (tensorProductIso R M N).symm))).trans
    (tensorStalkEquiv R M N x)

/-- `tensorObjStalkEquiv` sends the germ of the forgetful tensor image of a pure tensor `m ⊗ₜ n` to
the tensor product of the germs of `m` and `n`. -/
@[simp]
theorem tensorObjStalkEquiv_germ_forget_μ (M N : _root_.SheafOfModules.{u} (ringCatSheaf R))
    (x : X) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, sheafCompose_obj_obj,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (tensorObjStalkEquiv R M N x
        (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
          (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
            (op U)).hom (m ⊗ₜ[R.obj.obj (op U)] n))) =
      TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
        TopCat.Presheaf.germ N.val.presheaf U x hx n) := by
  let e : M ⊗ N ≅ tensorProduct R M N := M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm
  have h1 : tensorObjStalkEquiv R M N x
      (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
        (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
          (op U)).hom (m ⊗ₜ[R.obj.obj (op U)] n))) =
      tensorStalkEquiv R M N x
        (PresheafOfModules.stalkMapCommRing (S := R.obj) x e.hom.val
          (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
            (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
              (op U)).hom (m ⊗ₜ[R.obj.obj (op U)] n)))) :=
    congrArg (tensorStalkEquiv R M N x) (PresheafOfModules.stalkLinearEquivCommRing_apply x _ _)
  have h2 : PresheafOfModules.stalkMapCommRing (S := R.obj) x e.hom.val
      (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
        (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
          (op U)).hom (m ⊗ₜ[R.obj.obj (op U)] n))) =
      TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx
        ((tensorProductIso R M N).inv.val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
            (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[R.obj.obj (op U)] n))) := by
    erw [PresheafOfModules.stalkMapCommRing_germ]
    refine congrArg (TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx) ?_
    have hunit := congrArg (fun p ↦ (p.app (op U)).hom (m ⊗ₜ[R.obj.obj (op U)] n))
      ((forget_μ_comp_tensorUnderlyingIso_hom R M N).trans
        (sheafificationForgetAdjunction_unit_app R (M.val ⊗ N.val)))
    exact congrArg (fun z ↦ (tensorProductIso R M N).inv.val.app (op U) z) hunit
  refine h1.trans ((congrArg (tensorStalkEquiv R M N x) h2).trans ?_)
  erw [tensorStalkEquiv_apply, tensorStalkComparison_germ_unit_tmul]

/-- The inverse of `tensorObjStalkEquiv` sends a tensor of germs `m_x ⊗ₜ n_x` to the germ of the
forgetful tensor image of `m ⊗ₜ n`. -/
@[simp]
theorem tensorObjStalkEquiv_symm_tmul_germ (M N : _root_.SheafOfModules.{u} (ringCatSheaf R))
    (x : X) (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, sheafCompose_obj_obj,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((tensorObjStalkEquiv R M N x).symm
        (TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
          TopCat.Presheaf.germ N.val.presheaf U x hx n) =
      TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
        (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
          (op U)).hom (m ⊗ₜ[R.obj.obj (op U)] n))) :=
  (tensorObjStalkEquiv R M N x).symm_apply_eq.mpr
    (tensorObjStalkEquiv_germ_forget_μ R M N x U hx m n).symm

end Stalk

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
  have hmem :
      ((adj.unit.app E ⊗ₘ adj.unit.app F).val.app (op U)).hom
          (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app
            (op U)).hom (e ⊗ₜ[𝒪X.obj.obj (op U)] g)) =
        ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X))
          ((_root_.SheafOfModules.pushforward φ).obj
            ((_root_.SheafOfModules.pullback.{u} φ).obj E))
          ((_root_.SheafOfModules.pushforward φ).obj
            ((_root_.SheafOfModules.pullback.{u} φ).obj F))).app (op U)).hom
          (pullbackUnitApp φ E U e ⊗ₜ[𝒪X.obj.obj (op U)] pullbackUnitApp φ F U g) :=
    hnat
  exact hadj.trans ((congrArg ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ)
    ((_root_.SheafOfModules.pullback.{u} φ).obj E)
    ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.app (op U)) hmem).trans hpush)

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
    (show _ ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)] _ from
      (tensorObjStalkEquiv 𝒪X E F (f y)).baseChange
        ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
        ↑(TopCat.Presheaf.stalk (E ⊗ F).val.presheaf (f y))
        (↑(TopCat.Presheaf.stalk E.val.presheaf (f y)) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
          ↑(TopCat.Presheaf.stalk F.val.presheaf (f y)))).trans <|
      (TensorProduct.AlgebraTensorModule.distribBaseChange
          ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
          ↑(TopCat.Presheaf.stalk E.val.presheaf (f y))
          ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))).trans <|
        (show _ ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)] _ from
          TensorProduct.congr (pullbackStalkEquiv φ E y) (pullbackStalkEquiv φ F y)).trans
          (show _ ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)] _ from
            (tensorObjStalkEquiv 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
              ((_root_.SheafOfModules.pullback.{u} φ).obj F) y).symm)

private lemma pullbackTensorStalkEquiv_tmul_symm_tmul
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
  have h1 :
      (pullbackStalkEquiv φ (E ⊗ F) y).symm
        (pullbackStalkEquiv φ (E ⊗ F) y
          (a ⊗ₜ ((tensorObjStalkEquiv 𝒪X E F (f y)).symm (s ⊗ₜ t)))) =
        a ⊗ₜ ((tensorObjStalkEquiv 𝒪X E F (f y)).symm (s ⊗ₜ t)) :=
    (pullbackStalkEquiv φ (E ⊗ F) y).symm_apply_apply _
  have h2 :
      ((tensorObjStalkEquiv 𝒪X E F (f y)).baseChange
          ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
          ↑(TopCat.Presheaf.stalk (E ⊗ F).val.presheaf (f y))
          (↑(TopCat.Presheaf.stalk E.val.presheaf (f y)) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
            ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))))
        (a ⊗ₜ ((tensorObjStalkEquiv 𝒪X E F (f y)).symm (s ⊗ₜ t))) =
        a ⊗ₜ (s ⊗ₜ t) :=
    (LinearEquiv.baseChange_tmul _ _ _ _ _ _).trans
      (congrArg (a ⊗ₜ ·) ((tensorObjStalkEquiv 𝒪X E F (f y)).apply_symm_apply _))
  have h3 :
      TensorProduct.AlgebraTensorModule.distribBaseChange
          ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
          ↑(TopCat.Presheaf.stalk E.val.presheaf (f y))
          ↑(TopCat.Presheaf.stalk F.val.presheaf (f y)) (a ⊗ₜ (s ⊗ₜ t)) =
        (a ⊗ₜ s) ⊗ₜ (1 ⊗ₜ t) :=
    rfl
  have h4 :
      TensorProduct.congr (pullbackStalkEquiv φ E y) (pullbackStalkEquiv φ F y)
          ((a ⊗ₜ s) ⊗ₜ (1 ⊗ₜ t)) =
        pullbackStalkEquiv φ E y (a ⊗ₜ s) ⊗ₜ pullbackStalkEquiv φ F y (1 ⊗ₜ t) :=
    rfl
  have s1 := (congrArg
    ((tensorObjStalkEquiv 𝒪X E F (f y)).baseChange
      ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
      ↑(TopCat.Presheaf.stalk (E ⊗ F).val.presheaf (f y))
      (↑(TopCat.Presheaf.stalk E.val.presheaf (f y)) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        ↑(TopCat.Presheaf.stalk F.val.presheaf (f y)))) h1).trans h2
  have s2 := (congrArg
    (TensorProduct.AlgebraTensorModule.distribBaseChange
      ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
      ↑(TopCat.Presheaf.stalk E.val.presheaf (f y))
      ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))) s1).trans h3
  have s3 := (congrArg
    (TensorProduct.congr (pullbackStalkEquiv φ E y) (pullbackStalkEquiv φ F y)) s2).trans h4
  exact congrArg (tensorObjStalkEquiv 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
    ((_root_.SheafOfModules.pullback.{u} φ).obj F) y).symm s3

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
  have hL1 :
      (tensorObjStalkEquiv 𝒪X E F (f y)).symm
        (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV e' ⊗ₜ
          TopCat.Presheaf.germ F.val.presheaf V (f y) hyV g) =
        TopCat.Presheaf.germ (E ⊗ F).val.presheaf V (f y) hyV
          (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app
            (op V)).hom (e' ⊗ₜ[𝒪X.obj.obj (op V)] g)) := by
    simpa only [PresheafOfModules.presheaf_obj_coe, sheafCompose_obj_obj,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj] using
      tensorObjStalkEquiv_symm_tmul_germ 𝒪X E F (f y) V hyV e' g
  have hL2 :
      pullbackStalkEquiv φ (E ⊗ F) y
        (a ⊗ₜ ((tensorObjStalkEquiv 𝒪X E F (f y)).symm
          (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV e' ⊗ₜ
            TopCat.Presheaf.germ F.val.presheaf V (f y) hyV g))) =
        a • TopCat.Presheaf.germ
          ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)).val.presheaf
          ((Opens.map f).obj V) y hyV
          (pullbackUnitApp φ (E ⊗ F) V
            (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) E F).app
              (op V)).hom (e' ⊗ₜ[𝒪X.obj.obj (op V)] g))) := by
    rw [hL1]
    exact pullbackStalkEquiv_tmul_germ φ (E ⊗ F) y a V hyV _
  have hL3 :
      PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
          (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F).val
          (TopCat.Presheaf.germ
            ((_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F)).val.presheaf
            ((Opens.map f).obj V) y hyV
            (pullbackUnitApp φ (E ⊗ F) V
              (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X))
                E F).app (op V)).hom (e' ⊗ₜ[𝒪X.obj.obj (op V)] g)))) =
        TopCat.Presheaf.germ
          (((_root_.SheafOfModules.pullback.{u} φ).obj E) ⊗
            ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.presheaf
          ((Opens.map f).obj V) y hyV
          (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪Y))
              ((_root_.SheafOfModules.pullback.{u} φ).obj E)
              ((_root_.SheafOfModules.pullback.{u} φ).obj F)).app
              (op ((Opens.map f).obj V))).hom
            (pullbackUnitApp φ E V e' ⊗ₜ[𝒪Y.obj.obj (op ((Opens.map f).obj V))]
              pullbackUnitApp φ F V g)) :=
    (PresheafOfModules.stalkMapCommRing_germ _ _ _ _ _).trans <|
      congrArg (TopCat.Presheaf.germ
        (((_root_.SheafOfModules.pullback.{u} φ).obj E) ⊗
          ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.presheaf
        ((Opens.map f).obj V) y hyV)
        (pullback_δ_app_pullbackUnitApp_forget_μ φ E F V e' g)
  exact (congrArg _ hL2).trans ((map_smul _ _ _).trans (congrArg (a • ·) hL3))

private lemma pullbackTensorStalkEquiv_tmul_germ
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y)
    (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)) (V : Opens X) (hyV : f y ∈ V)
    (e' : E.val.obj (op V)) (g : F.val.obj (op V)) :
    letI := stalkAlgebra φ y
    pullbackTensorStalkEquiv φ E F y
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
  have hR1 :
      pullbackStalkEquiv φ E y (a ⊗ₜ TopCat.Presheaf.germ E.val.presheaf V (f y) hyV e') =
        a • TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj E).val.presheaf
          ((Opens.map f).obj V) y hyV (pullbackUnitApp φ E V e') :=
    pullbackStalkEquiv_tmul_germ φ E y a V hyV e'
  have hR2 :
      pullbackStalkEquiv φ F y (1 ⊗ₜ TopCat.Presheaf.germ F.val.presheaf V (f y) hyV g) =
        TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj F).val.presheaf
          ((Opens.map f).obj V) y hyV (pullbackUnitApp φ F V g) :=
    (pullbackStalkEquiv_tmul_germ φ F y 1 V hyV g).trans (one_smul _ _)
  have hR3 :
      (tensorObjStalkEquiv 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
        ((_root_.SheafOfModules.pullback.{u} φ).obj F) y).symm
        (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj E).val.presheaf
            ((Opens.map f).obj V) y hyV (pullbackUnitApp φ E V e') ⊗ₜ
          TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj F).val.presheaf
            ((Opens.map f).obj V) y hyV (pullbackUnitApp φ F V g)) =
        TopCat.Presheaf.germ
          (((_root_.SheafOfModules.pullback.{u} φ).obj E) ⊗
            ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.presheaf
          ((Opens.map f).obj V) y hyV
          (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪Y))
              ((_root_.SheafOfModules.pullback.{u} φ).obj E)
              ((_root_.SheafOfModules.pullback.{u} φ).obj F)).app
              (op ((Opens.map f).obj V))).hom
            (pullbackUnitApp φ E V e' ⊗ₜ[𝒪Y.obj.obj (op ((Opens.map f).obj V))]
              pullbackUnitApp φ F V g)) := by
    simpa only [PresheafOfModules.presheaf_obj_coe, sheafCompose_obj_obj,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj] using
      tensorObjStalkEquiv_symm_tmul_germ 𝒪Y
        ((_root_.SheafOfModules.pullback.{u} φ).obj E)
        ((_root_.SheafOfModules.pullback.{u} φ).obj F)
        y ((Opens.map f).obj V) hyV (pullbackUnitApp φ E V e') (pullbackUnitApp φ F V g)
  exact (pullbackTensorStalkEquiv_tmul_symm_tmul φ E F y a _ _).trans <|
    (congrArg (tensorObjStalkEquiv 𝒪Y ((_root_.SheafOfModules.pullback.{u} φ).obj E)
      ((_root_.SheafOfModules.pullback.{u} φ).obj F) y).symm
      ((congrArg₂ (· ⊗ₜ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)] ·) hR1 hR2).trans
        (TensorProduct.smul_tmul' a _ _))).trans <|
      (LinearEquiv.map_smul _ a _).trans (congrArg (a • ·) hR3)

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
      exact (stalkMapCommRing_pullback_δ_tmul_germ φ E F y a V hyV e' g).trans
        (pullbackTensorStalkEquiv_tmul_germ φ E F y a V hyV e' g).symm

/-- **Invertibility of the pullback tensor comparison.** For every morphism of ringed spaces
`(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)` and all sheaves of `𝒪_X`-modules `E` and `F`, the canonical oplax
tensor comparison `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` is an isomorphism, without any flatness,
finiteness, or quasi-coherence assumptions (Stacks Project, Tag 01CD). -/
instance isIso_pullback_δ (E F : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) := by
  rw [isIso_iff_forall_bijective_stalkMapCommRing]
  intro y
  rw [stalkMapCommRing_pullback_δ]
  exact (pullbackTensorStalkEquiv φ E F y).bijective

/-- For every morphism of ringed spaces `(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)`, the canonical oplax unit
comparison `η : f^* 𝒪_X ⟶ 𝒪_Y` is an isomorphism. -/
instance isIso_pullback_η :
    IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ)) := by
  have h := _root_.SheafOfModules.pullback_η φ
  rw [h]
  exact _root_.SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal φ

/-- Pullback of sheaves of modules along a morphism of ringed spaces is strong monoidal, with
inverse comparisons inherited from `SheafOfModules.pullbackOplaxMonoidal`. -/
@[instance_reducible]
def pullbackMonoidal : (_root_.SheafOfModules.pullback.{u} φ).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} φ)

attribute [instance] pullbackMonoidal

/-- Pullback of sheaves of modules along a morphism of ringed spaces is strong symmetric
monoidal. -/
@[instance_reducible]
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
@[simp]
theorem pullback_ε :
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ) =
      inv (_root_.SheafOfModules.pullbackObjUnitToUnit φ) := by
  apply IsIso.eq_inv_of_hom_inv_id
  have h := _root_.SheafOfModules.pullback_η φ
  rw [← h]
  exact Functor.Monoidal.η_ε (_root_.SheafOfModules.pullback.{u} φ)

end RingedSpace

section Identity

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- The unit comparison for identity pullback is an isomorphism. -/
theorem isIso_pullback_id_η :
    letI := _root_.SheafOfModules.pullbackOplaxMonoidal
      (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))) := by
  let := _root_.SheafOfModules.pullbackOplaxMonoidal
    (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  rw [pullback_id_η]
  infer_instance

/-- The tensor comparison for identity pullback is an isomorphism. -/
theorem isIso_pullback_id_δ (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    letI := _root_.SheafOfModules.pullbackOplaxMonoidal
      (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M N) := by
  let := _root_.SheafOfModules.pullbackOplaxMonoidal
    (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  have : IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M N ≫
      ((_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app M ⊗ₘ
        (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app N)) := by
    rw [pullback_id_δ]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app M ⊗ₘ
      (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app N)

/-- The canonical identity isomorphism `SheafOfModules.pullbackId` respects the strong monoidal
structure on identity pullback. -/
theorem isMonoidal_pullbackId_hom :
    letI := _root_.SheafOfModules.pullbackOplaxMonoidal
      (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    letI := isIso_pullback_id_η R
    letI := isIso_pullback_id_δ R
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom
      inferInstance Functor.LaxMonoidal.id := by
  let := _root_.SheafOfModules.pullbackOplaxMonoidal
    (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  let := isIso_pullback_id_η R
  let := isIso_pullback_id_δ R
  let := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
    (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
  refine { unit := ?_, tensor := fun E F ↦ ?_ }
  · rw [← pullback_id_η R]
    exact Functor.Monoidal.ε_η _
  · rw [← cancel_epi (Functor.OplaxMonoidal.δ
      (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) E F)]
    simp [pullback_id_δ]

/-- The strong monoidal unit map of identity pullback inverts the canonical identity isomorphism
at the structure sheaf. -/
theorem pullback_id_ε :
    letI := _root_.SheafOfModules.pullbackOplaxMonoidal
      (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    letI := isIso_pullback_id_η R
    letI := isIso_pullback_id_δ R
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) =
      (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).inv.app (𝟙_ _) := by
  let := _root_.SheafOfModules.pullbackOplaxMonoidal
    (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  let := isIso_pullback_id_η R
  let := isIso_pullback_id_δ R
  let := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
    (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
  rw [← cancel_mono ((_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app (𝟙_ _))]
  have hu := @NatTrans.IsMonoidal.unit _ _ _ _ _ _ _ _
    (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom _ Functor.LaxMonoidal.id
    (isMonoidal_pullbackId_hom R)
  exact hu.trans (by simp)

/-- The strong monoidal tensor map of identity pullback intertwines the canonical identity
isomorphism with the tensor product of identity comparisons. -/
@[reassoc]
theorem pullback_id_μ (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    letI := _root_.SheafOfModules.pullbackOplaxMonoidal
      (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
    letI := isIso_pullback_id_η R
    letI := isIso_pullback_id_δ R
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
      (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
        (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))) M N ≫
      (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app (M ⊗ N) =
      (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app M ⊗ₘ
        (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom.app N := by
  let := _root_.SheafOfModules.pullbackOplaxMonoidal
    (S := R) (R := R) (F := 𝟭 C) (𝟙 (ringCatSheaf R))
  let := isIso_pullback_id_η R
  let := isIso_pullback_id_δ R
  let := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} (J := J) (K := J)
    (S := ringCatSheaf R) (R := ringCatSheaf R) (F := 𝟭 C) (𝟙 (ringCatSheaf R)))
  have ht := @NatTrans.IsMonoidal.tensor _ _ _ _ _ _ _ _
    (_root_.SheafOfModules.pullbackId (ringCatSheaf R)).hom _ Functor.LaxMonoidal.id
    (isMonoidal_pullbackId_hom R) M N
  exact ht.trans (by simp)

end Identity

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
theorem isIso_pullback_comp_η :
    IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u}
      (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))) := by
  rw [_root_.SheafOfModules.pullback_comp_η φ ψ]
  infer_instance

/-- The tensor comparison for a composite pullback of sheaves of modules on ringed spaces is an
isomorphism. -/
theorem isIso_pullback_comp_δ (M N : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u}
      (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) M N) := by
  rw [_root_.SheafOfModules.pullback_comp_δ φ ψ M N]
  infer_instance

/-- The canonical composition isomorphism `SheafOfModules.pullbackComp` respects the strong
monoidal structures of module pullbacks along morphisms of ringed spaces. -/
theorem isMonoidal_pullbackComp_hom :
    letI := isIso_pullback_comp_η φ ψ
    letI := isIso_pullback_comp_δ φ ψ
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u}
      (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))
    NatTrans.IsMonoidal (_root_.SheafOfModules.pullbackComp φ ψ).hom := by
  let := isIso_pullback_comp_η φ ψ
  let := isIso_pullback_comp_δ φ ψ
  let := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u}
    (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))
  refine { unit := ?_, tensor := fun M N ↦ ?_ }
  · rw [← cancel_mono (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u}
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
      have hc := _root_.SheafOfModules.pullback_comp_η φ ψ
      rw [Functor.OplaxMonoidal.comp_η,
        ← cancel_epi ((_root_.SheafOfModules.pullbackComp φ ψ).inv.app (𝟙_ _)),
        Iso.inv_hom_id_app_assoc]
      exact hc
    rw [hη]
    exact (Functor.Monoidal.ε_η (_root_.SheafOfModules.pullback.{u} φ ⋙
      _root_.SheafOfModules.pullback.{u} ψ)).trans (Functor.Monoidal.ε_η _).symm
  · rw [← cancel_epi (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ ⋙
        _root_.SheafOfModules.pullback.{u} ψ) M N),
      ← cancel_mono (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u}
        (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z)
        (R := ringCatSheaf 𝒪Z) (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) M N)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    have hδ := _root_.SheafOfModules.pullback_comp_δ φ ψ M N
    rw [Functor.OplaxMonoidal.comp_δ]
    rw [← cancel_epi ((_root_.SheafOfModules.pullbackComp φ ψ).inv.app (M ⊗ N)),
      Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc] using hδ

/-- The strong monoidal unit map of a composite pullback is the composite of the unit maps through
`SheafOfModules.pullbackComp`. -/
@[reassoc]
theorem pullback_comp_ε :
    letI := isIso_pullback_comp_η φ ψ
    letI := isIso_pullback_comp_δ φ ψ
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u}
      (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} ψ) ≫
        (_root_.SheafOfModules.pullback.{u} ψ).map
          (Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ)) ≫
        (_root_.SheafOfModules.pullbackComp φ ψ).hom.app (𝟙_ _) =
      Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u}
        (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
        (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) := by
  let := isIso_pullback_comp_η φ ψ
  let := isIso_pullback_comp_δ φ ψ
  let := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u}
    (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))
  have hu := @NatTrans.IsMonoidal.unit _ _ _ _ _ _ _ _
    (_root_.SheafOfModules.pullbackComp φ ψ).hom _ _ (isMonoidal_pullbackComp_hom φ ψ)
  rw [Functor.LaxMonoidal.comp_ε, Category.assoc] at hu
  exact hu

/-- The strong monoidal tensor map of a composite pullback is the composite of the tensor maps
through `SheafOfModules.pullbackComp`. -/
@[reassoc]
theorem pullback_comp_μ
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) :
    letI := isIso_pullback_comp_η φ ψ
    letI := isIso_pullback_comp_δ φ ψ
    letI := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u}
      (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))
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
  let := isIso_pullback_comp_η φ ψ
  let := isIso_pullback_comp_δ φ ψ
  let := Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u}
    (F := Opens.map f ⋙ Opens.map g) (K := Opens.grothendieckTopology Z) (R := ringCatSheaf 𝒪Z)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))
  have ht := @NatTrans.IsMonoidal.tensor _ _ _ _ _ _ _ _
    (_root_.SheafOfModules.pullbackComp φ ψ).hom _ _ (isMonoidal_pullbackComp_hom φ ψ) M N
  rw [Functor.LaxMonoidal.comp_μ, Category.assoc] at ht
  exact ht

end Composition

end SheafOfModules

end

end TauCeti
