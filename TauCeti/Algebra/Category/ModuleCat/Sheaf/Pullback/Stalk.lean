/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Stalk

/-!
# Stalks of the pullback of a sheaf of modules

Let `(f, φ) : (Y, 𝒪_Y) → (X, 𝒪_X)` be a morphism of ringed spaces, `G` an `𝒪_X`-module and
`y ∈ Y`. The stalk of the pullback `f^* G = SheafOfModules.pullback φ G` at `y` is the extension
of scalars of the stalk of `G` at `f y` along the stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}`:
`𝒪_{Y,y} ⊗_{𝒪_{X,f(y)}} G_{f(y)} ≅ (f^* G)_y`, `a ⊗ m_{f(y)} ↦ a · (η m)_y`, where `η` is the unit
of the adjunction between pullback and pushforward (Stacks Project, Tag 0098). No hypothesis is
made on `G`.

Mathlib defines `f^*` only as a left adjoint, so the stalk is computed through universal
properties rather than by a colimit formula. For an `𝒪_{Y,y}`-module `T`, linear maps
`(f^* G)_y → T` are morphisms `f^* G ⟶ y_* T` into the skyscraper, hence morphisms
`G ⟶ f_* y_* T = (f y)_* T`, hence `𝒪_{X,f(y)}`-linear maps `G_{f(y)} → T`
(`TauCeti.SheafOfModules.pullbackStalkHomEquiv`). Both sides of the comparison therefore have the
same linear maps into every `T`, and the comparison is the map inducing this bijection.

## Main declarations

* `TauCeti.SheafOfModules.pullbackStalkHomEquiv`: linear maps out of `(f^* G)_y` are the
  `𝒪_{X,f(y)}`-linear maps out of `G_{f(y)}`, for `T` with `𝒪_{X,f(y)}` acting through the stalk
  map, through the germs of the unit;
* `TauCeti.SheafOfModules.pullbackStalkEquiv`: the linear equivalence
  `𝒪_{Y,y} ⊗_{𝒪_{X,f(y)}} G_{f(y)} ≃ (f^* G)_y`, computed on pure tensors by
  `TauCeti.SheafOfModules.pullbackStalkEquiv_tmul_germ`;
* `TauCeti.SheafOfModules.pullbackStalkEquiv_naturality`: its naturality in `G`.

## References

* The Stacks Project, *Sheaves on Spaces*, Tag 0098.
-/

public section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace TauCeti

noncomputable section

namespace SheafOfModules

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  (G : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)) (y : Y)

/-- The unit `G ⟶ f_* f^* G` of the adjunction between pullback and pushforward along `φ`, on
sections over `U`, with values in the sections of `f^* G` over `f⁻¹ U`. -/
abbrev pullbackUnitApp (U : Opens X) (m : G.val.obj (op U)) :
    ((_root_.SheafOfModules.pullback φ).obj G).val.obj (op ((Opens.map f).obj U)) :=
  ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m

section HomEquiv

variable (T : Type u) [AddCommGroup T] [Module ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) T]
  [Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) T]

/-- For an `𝒪_{Y,y}`-module `T` on which `𝒪_{X,f(y)}` acts through the stalk map of `(f, φ)`,
`𝒪_{Y,y}`-linear maps `(f^* G)_y → T` correspond to `𝒪_{X,f(y)}`-linear maps `G_{f(y)} → T`.
The bijection is the composite of the adjunction between stalk and skyscraper on `Y`, of the
adjunction between pullback and pushforward, of `f_* y_* T ≅ (f y)_* T`, and of the adjunction
between stalk and skyscraper on `X`. -/
def pullbackStalkHomEquiv
    (hT : ∀ (a : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))) (t : T),
      a • t = ringStalkMap φ y a • t) :
    (↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf y)
        →ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)] T) ≃
      (↑(TopCat.Presheaf.stalk G.val.presheaf (f y))
        →ₗ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))] T) :=
  (skyscraperHomEquiv y T _).trans <|
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv G
      (skyscraper 𝒪Y y T)).trans <|
      ((Iso.refl G).homCongr (pushforwardSkyscraperIso φ y T hT)).trans
        (skyscraperHomEquiv (f y) T G).symm

/-- The `𝒪_{X,f(y)}`-linear map attached to `g` sends the germ of `m` at `f y` to `g` of the
germ at `y` of the image of `m` under the unit. -/
@[simp]
theorem pullbackStalkHomEquiv_apply_germ
    (hT : ∀ (a : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))) (t : T),
      a • t = ringStalkMap φ y a • t)
    (g : ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf y)
      →ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)] T)
    (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    dsimp% only [sheafCompose_obj_obj, _root_.PresheafOfModules.presheaf_obj_coe,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (pullbackStalkHomEquiv φ G y T hT g (TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      g (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf
        ((Opens.map f).obj U) y hy (pullbackUnitApp φ G U m))) := by
  simp only [pullbackStalkHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Adjunction.homEquiv_unit]
  rw [skyscraperHomEquiv_symm_apply_germ]
  exact (pushforwardSkyscraperIso_hom_val_app_apply φ y T hT (op U) _ ⟨hy⟩).trans
    (skyscraperHomEquiv_apply_val_app_apply y T _ g _ _ ⟨hy⟩)

end HomEquiv

/-- `𝒪_{X,f(y)}` acts on the stalk `(f^* G)_y` through the stalk map of `(f, φ)`. -/
private abbrev pullbackStalkModule :
    Module ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf y) :=
  Module.compHom _ (ringStalkMap φ y).hom

/-- The `𝒪_{X,f(y)}`-linear map `G_{f(y)} → (f^* G)_y`, `m_{f(y)} ↦ (η m)_y`. -/
private def toPullbackStalk :
    letI := pullbackStalkModule φ G y
    ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) →ₗ[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf y) :=
  letI := pullbackStalkModule φ G y
  pullbackStalkHomEquiv φ G y _ (fun _ _ ↦ rfl) LinearMap.id

private lemma toPullbackStalk_germ (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    toPullbackStalk φ G y (TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf
        ((Opens.map f).obj U) y hy (pullbackUnitApp φ G U m) :=
  letI := pullbackStalkModule φ G y
  pullbackStalkHomEquiv_apply_germ φ G y _ (fun _ _ ↦ rfl) LinearMap.id U hy m

/-- The comparison `𝒪_{Y,y} ⊗_{𝒪_{X,f(y)}} G_{f(y)} → (f^* G)_y`, `a ⊗ m_{f(y)} ↦ a · (η m)_y`,
where `η : G ⟶ f_* f^* G` is the unit of the adjunction between pullback and pushforward. -/
private def pullbackStalkComparison :
    letI := stalkAlgebra φ y
    ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        ↑(TopCat.Presheaf.stalk G.val.presheaf (f y))
      →ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf y) :=
  letI := stalkAlgebra φ y
  letI := pullbackStalkModule φ G y
  haveI : IsScalarTower ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)) ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf y) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  (toPullbackStalk φ G y).liftBaseChange _

private lemma pullbackStalkComparison_tmul_germ (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y))
    (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI := stalkAlgebra φ y
    pullbackStalkComparison φ G y (a ⊗ₜ TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      a • TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf
        ((Opens.map f).obj U) y hy (pullbackUnitApp φ G U m) :=
  congrArg (a • ·) (toPullbackStalk_germ φ G y U hy m)

/-- The inverse of the comparison: the `𝒪_{Y,y}`-linear map `(f^* G)_y → 𝒪_{Y,y} ⊗ G_{f(y)}`
corresponding to `m_{f(y)} ↦ 1 ⊗ m_{f(y)}` under `pullbackStalkHomEquiv`. -/
private def ofPullbackStalk :
    letI := stalkAlgebra φ y
    ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf y)
      →ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
          ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) :=
  letI := stalkAlgebra φ y
  (pullbackStalkHomEquiv φ G y _ fun a t ↦ (algebraMap_smul _ a t).symm).symm
    (TensorProduct.mk _ _ _ 1)

private lemma ofPullbackStalk_germ (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI := stalkAlgebra φ y
    ofPullbackStalk φ G y (TopCat.Presheaf.germ
        ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
          (pullbackUnitApp φ G U m)) =
      1 ⊗ₜ TopCat.Presheaf.germ G.val.presheaf U (f y) hy m := by
  let := stalkAlgebra φ y
  have hT : ∀ (a : ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y)))
      (t : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        ↑(TopCat.Presheaf.stalk G.val.presheaf (f y))), a • t = ringStalkMap φ y a • t :=
    fun a t ↦ (algebraMap_smul _ a t).symm
  refine (pullbackStalkHomEquiv_apply_germ φ G y _ hT _ U hy m).symm.trans ?_
  rw [ofPullbackStalk, Equiv.apply_symm_apply]
  exact TensorProduct.mk_apply _ _

/-- The stalk of the pullback of a sheaf of modules along a morphism of ringed spaces `(f, φ)` is
the extension of scalars of the stalk at `f y` along the stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}`:
`𝒪_{Y,y} ⊗_{𝒪_{X,f(y)}} G_{f(y)} ≃ (f^* G)_y`, `a ⊗ m_{f(y)} ↦ a · (η m)_y`, for every
`𝒪_X`-module `G` (Stacks Project, Tag 0098). -/
def pullbackStalkEquiv :
    letI := stalkAlgebra φ y
    ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        ↑(TopCat.Presheaf.stalk G.val.presheaf (f y))
      ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf y) :=
  letI := stalkAlgebra φ y
  letI := pullbackStalkModule φ G y
  LinearEquiv.ofLinearMap (pullbackStalkComparison φ G y) (ofPullbackStalk φ G y)
    ((pullbackStalkHomEquiv φ G y _ fun _ _ ↦ rfl).injective <| LinearMap.ext fun s ↦ by
      obtain ⟨U, hy, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf s
      -- Both sides send `m_{f(y)}` to `(η m)_y`.
      refine (pullbackStalkHomEquiv_apply_germ φ G y _ _ _ U hy m).trans ?_
      refine (congrArg (pullbackStalkComparison φ G y) (ofPullbackStalk_germ φ G y U hy m)).trans ?_
      refine (pullbackStalkComparison_tmul_germ φ G y 1 U hy m).trans ?_
      rw [one_smul]
      exact (toPullbackStalk_germ φ G y U hy m).symm)
    (TensorProduct.AlgebraTensorModule.ext fun a s ↦ by
      obtain ⟨U, hy, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf s
      -- Both sides send `a ⊗ m_{f(y)}` to `a ⊗ m_{f(y)}`.
      refine (congrArg (ofPullbackStalk φ G y)
        (pullbackStalkComparison_tmul_germ φ G y a U hy m)).trans ?_
      refine ((ofPullbackStalk φ G y).map_smul a _).trans ?_
      refine (congrArg (a • ·) (ofPullbackStalk_germ φ G y U hy m)).trans ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, LinearMap.id_apply])

/-- The equivalence sends `a ⊗ m_{f(y)}` to `a · (η m)_y`. -/
@[simp]
theorem pullbackStalkEquiv_tmul_germ (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y))
    (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    dsimp% only [sheafCompose_obj_obj, _root_.PresheafOfModules.presheaf_obj_coe,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (letI := stalkAlgebra φ y
    pullbackStalkEquiv φ G y (a ⊗ₜ TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      a • TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf
        ((Opens.map f).obj U) y hy (pullbackUnitApp φ G U m)) :=
  pullbackStalkComparison_tmul_germ φ G y a U hy m

/-- The inverse equivalence sends `(η m)_y` to `1 ⊗ m_{f(y)}`. -/
@[simp]
theorem pullbackStalkEquiv_symm_germ (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    dsimp% only [sheafCompose_obj_obj, _root_.PresheafOfModules.presheaf_obj_coe,
      Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (letI := stalkAlgebra φ y
    (pullbackStalkEquiv φ G y).symm (TopCat.Presheaf.germ
        ((_root_.SheafOfModules.pullback φ).obj G).val.presheaf ((Opens.map f).obj U) y hy
          (pullbackUnitApp φ G U m)) =
      1 ⊗ₜ TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) :=
  ofPullbackStalk_germ φ G y U hy m

/-- The stalk equivalence is natural in the `𝒪_X`-module, on pure tensors: for `g : G ⟶ G'`, it
sends `a ⊗ g_{f(y)}(s)` to the image under the stalk map of `f^* g` of the image of `a ⊗ s`. -/
theorem pullbackStalkEquiv_naturality_apply {G' : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)}
    (g : G ⟶ G') (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y))
    (s : ↑(TopCat.Presheaf.stalk G.val.presheaf (f y))) :
    letI := stalkAlgebra φ y
    pullbackStalkEquiv φ G' y
        (a ⊗ₜ PresheafOfModules.stalkMapCommRing (S := 𝒪X.obj) (f y) g.val s) =
      PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
        ((_root_.SheafOfModules.pullback φ).map g).val (pullbackStalkEquiv φ G y (a ⊗ₜ s)) := by
  let := stalkAlgebra φ y
  obtain ⟨U, hy, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf s
  -- The unit is natural: `η_{G'} (g m) = (f_* f^* g) (η_G m)`.
  have hη : pullbackUnitApp φ G' U (g.val.app (op U) m) =
      ((_root_.SheafOfModules.pullback φ).map g).val.app (op ((Opens.map f).obj U))
        (pullbackUnitApp φ G U m) :=
    congr(($((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.naturality g)).val.app
      (op U) m)
  dsimp only [_root_.PresheafOfModules.presheaf_obj_coe] at m hη ⊢
  rw [PresheafOfModules.stalkMapCommRing_germ, pullbackStalkEquiv_tmul_germ,
    pullbackStalkEquiv_tmul_germ, map_smul, hη]
  exact congrArg (a • ·) (PresheafOfModules.stalkMapCommRing_germ (S := 𝒪Y.obj) y _ _ hy _).symm

/-- The stalk equivalence is natural in the `𝒪_X`-module: for `g : G ⟶ G'`, it intertwines the
base change of the stalk map of `g` at `f y` with the stalk map of `f^* g` at `y`. -/
theorem pullbackStalkEquiv_naturality {G' : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X)}
    (g : G ⟶ G') :
    letI := stalkAlgebra φ y
    (pullbackStalkEquiv φ G' y).toLinearMap ∘ₗ
        LinearMap.baseChange _ (PresheafOfModules.stalkMapCommRing (S := 𝒪X.obj) (f y) g.val) =
      PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
          ((_root_.SheafOfModules.pullback φ).map g).val ∘ₗ
        (pullbackStalkEquiv φ G y).toLinearMap := by
  let := stalkAlgebra φ y
  refine LinearMap.ext fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul a s => exact pullbackStalkEquiv_naturality_apply φ G y g a s
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

end SheafOfModules

end

end TauCeti
