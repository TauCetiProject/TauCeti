/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Skyscraper

/-!
# Stalks of pulled-back sheaves of modules

Constructs `SheafOfModules.stalkRingHom`, `unitStalkEquiv`, `pullbackStalkComparison`, and the
canonical stalk isomorphism `pullbackStalkEquiv : R_y ⊗[S_{f(y)}] G_{f(y)} ≃ₗ[R_y] (f^* G)_y`
via Yoneda against `skyscraperCommRing`, with naturality and composition compatibilities (Tag 0098).
-/

public section

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf
open TauCeti.SheafOfModules (commRingCatHom ringCatSheaf)
open scoped TensorProduct
universe u
noncomputable section
namespace SheafOfModules
section
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf R))

/-- The ring homomorphism `S_{f(y)} ⟶ R_y` on stalks induced by `(f, φ)`. -/
def stalkRingHom (y : Y) : stalk S.obj (f y) ⟶ stalk R.obj y :=
  (stalkFunctor CommRingCat.{u} (f y)).map (commRingCatHom.{u, u, u, u, u} φ) ≫
    stalkPushforward CommRingCat.{u} f R.obj y
@[reassoc (attr := simp)] theorem stalkRingHom_germ (y : Y) (U : Opens X) (hy : f y ∈ U) :
    germ S.obj U (f y) hy ≫ stalkRingHom f φ y =
      (commRingCatHom.{u, u, u, u, u} φ).app (op U) ≫
        germ R.obj ((Opens.map f).obj U) y (Opens.mem_map.mpr hy) := by
  rw [stalkRingHom]; erw [stalkFunctor_map_germ_assoc, stalkPushforward_germ]
@[simp]
theorem stalkRingHom_germ_apply (y : Y) (U : Opens X) (hy : f y ∈ U) (r : S.obj.obj (op U)) :
    stalkRingHom f φ y (germ S.obj U (f y) hy r) =
      germ R.obj ((Opens.map f).obj U) y (Opens.mem_map.mpr hy) (φ.hom.app (op U) r) :=
  ConcreteCategory.congr_hom (stalkRingHom_germ f φ y U hy) r
@[simp] theorem stalkRingHom_id (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X) :
    stalkRingHom (𝟙 X) (𝟙 (ringCatSheaf S)) x = 𝟙 (stalk S.obj x) := by
  refine stalk_hom_ext S.obj fun U hx ↦ ?_
  ext r; exact stalkRingHom_germ_apply (𝟙 X) (𝟙 (ringCatSheaf S)) x U hx r

/-- The composite morphism of underlying sheaves of rings along `g ≫ f`. -/
@[expose] def compRingCatSheafHom {Z : TopCat.{u}} (g : Z ⟶ Y)
    {Q : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (ψ : ringCatSheaf R ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q)) :
    ringCatSheaf S ⟶
      ((Opens.map (g ≫ f)).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q) :=
  φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).map ψ
theorem stalkRingHom_comp {Z : TopCat.{u}} (g : Z ⟶ Y)
    {Q : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (ψ : ringCatSheaf R ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q)) (z : Z) :
    stalkRingHom (g ≫ f) (compRingCatSheafHom f φ g ψ) z =
      stalkRingHom f φ (g z) ≫ stalkRingHom g ψ z := by
  refine stalk_hom_ext S.obj fun U hz ↦ ?_
  ext r
  exact (stalkRingHom_germ_apply (g ≫ f) (compRingCatSheafHom f φ g ψ) z U hz r).trans
    ((stalkRingHom_germ_apply g ψ z ((Opens.map f).obj U) (Opens.mem_map.mpr hz)
      (φ.hom.app (op U) r)).symm.trans
      (congrArg (stalkRingHom g ψ z) (stalkRingHom_germ_apply f φ (g z) U hz r).symm))
end
section
variable {X : TopCat.{u}} (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)

private theorem unitStalkComparison_res {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (r : (unit (ringCatSheaf S)).val.obj (op V)) :
    (germ S.obj U x hx).hom.toAddMonoidHom ((unit (ringCatSheaf S)).val.map i.op r) =
      (germ S.obj V x (i.le hx)).hom.toAddMonoidHom r :=
  germ_res_apply S.obj i x hx r

/-- The canonical `S_x`-linear map `(unit (ringCatSheaf S))_x →ₗ[S_x] S_x`. -/
def unitStalkComparison :
    ↑(stalk (unit (ringCatSheaf S)).val.presheaf x) →ₗ[↑(stalk S.obj x)] ↑(stalk S.obj x) :=
  PresheafOfModules.stalkLiftCommRing (S := S.obj) x (unit (ringCatSheaf S)).val
    (fun U hx ↦ (germ S.obj U x hx).hom.toAddMonoidHom)
    (unitStalkComparison_res S x)
    (fun U hx r m ↦ map_mul (germ S.obj U x hx).hom r m)
@[simp] theorem unitStalkComparison_germ (U : Opens X) (hx : x ∈ U) (r : S.obj.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (unitStalkComparison S x (germ (unit (ringCatSheaf S)).val.presheaf U x hx r) =
      germ S.obj U x hx r) := by
  unfold unitStalkComparison; apply PresheafOfModules.stalkLiftCommRing_germ

/-- The canonical `S_x`-linear equivalence `(unit (ringCatSheaf S))_x ≃ₗ[S_x] S_x`. -/
def unitStalkEquiv :
    ↑(stalk (unit (ringCatSheaf S)).val.presheaf x) ≃ₗ[↑(stalk S.obj x)] ↑(stalk S.obj x) :=
  LinearEquiv.ofLinearMap (unitStalkComparison S x)
    (LinearMap.toSpanSingleton ↑(stalk S.obj x) _
      (germ (unit (ringCatSheaf S)).val.presheaf ⊤ x (Opens.mem_top x) (1 : S.obj.obj (op ⊤))))
    (LinearMap.ext fun a ↦ by
      simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply,
        map_smul]
      erw [unitStalkComparison_germ S x ⊤ (Opens.mem_top x) (1 : S.obj.obj (op ⊤))]
      rw [map_one (germ S.obj ⊤ x (Opens.mem_top x)).hom, smul_eq_mul, mul_one])
    (LinearMap.ext fun s ↦ by
      obtain ⟨U, hx, r, rfl⟩ := exists_germ_eq (unit (ringCatSheaf S)).val.presheaf s
      let r' : S.obj.obj (op U) := r
      let Q : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
        (unit (ringCatSheaf S)).val
      simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply]
      erw [unitStalkComparison_germ S x U hx r']
      rw [← germ_res_apply (unit (ringCatSheaf S)).val.presheaf (homOfLE (le_top : U ≤ ⊤)) x hx
        (1 : S.obj.obj (op ⊤))]
      exact (Q.germ_smul (R := S.obj) x U hx r' _).symm.trans
        (congrArg (germ (unit (ringCatSheaf S)).val.presheaf U x hx)
          ((congrArg (r' * ·) (map_one (S.obj.map (homOfLE (le_top : U ≤ ⊤)).op).hom)).trans
            (mul_one r'))))
@[simp] theorem unitStalkEquiv_apply (s : ↑(stalk (unit (ringCatSheaf S)).val.presheaf x)) :
    unitStalkEquiv S x s = unitStalkComparison S x s := (rfl)
theorem unitStalkEquiv_germ (U : Opens X) (hx : x ∈ U) (r : S.obj.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (unitStalkEquiv S x (germ (unit (ringCatSheaf S)).val.presheaf U x hx r) =
      germ S.obj U x hx r) :=
  unitStalkComparison_germ S x U hx r
@[simp] theorem unitStalkEquiv_symm_apply (a : ↑(stalk S.obj x)) :
    (unitStalkEquiv S x).symm a =
      a • germ (unit (ringCatSheaf S)).val.presheaf ⊤ x (Opens.mem_top x) (1 : S.obj.obj (op ⊤)) :=
  (rfl)
end
section PullbackStalk
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf R))
  [(pushforward.{u} φ).IsRightAdjoint]
private def pullbackStalkSectionMap (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (U : Opens X) (hy : f y ∈ U) :
    (G.val.obj (op U) : Type u) →+ ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
  (germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy).hom.comp
    (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U)).hom.toAddMonoidHom
private theorem pullbackStalkSectionMap_res (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    {U V : Opens X} (i : U ⟶ V) (hy : f y ∈ U) (m : G.val.obj (op V)) :
    pullbackStalkSectionMap f φ G y U hy (G.val.map i.op m) =
      pullbackStalkSectionMap f φ G y V (i.le hy) m :=
  (congrArg (germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj _) y hy)
    (PresheafOfModules.naturality_apply ((pullbackPushforwardAdjunction φ).unit.app G).val i.op
      m)).trans (germ_res_apply ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).map i) y hy _)
private theorem pullbackStalkSectionMap_smul (G : SheafOfModules.{u} (ringCatSheaf S))
    (y : Y) (U : Opens X) (hy : f y ∈ U) (r : S.obj.obj (op U)) (m : G.val.obj (op U)) :
    letI : Module ↑(stalk S.obj (f y)) ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
      Module.compHom _ (stalkRingHom f φ y).hom
    pullbackStalkSectionMap f φ G y U hy (r • m) =
      germ S.obj U (f y) hy r • pullbackStalkSectionMap f φ G y U hy m :=
  let _ : Module ↑(stalk S.obj (f y)) ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
    Module.compHom _ (stalkRingHom f φ y).hom
  let P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
    ((pullback.{u} φ).obj G).val
  (congrArg (germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y hy)
    ((((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U)).hom.map_smul r m)).trans
    ((P.germ_smul (R := R.obj) y ((Opens.map f).obj U) hy (φ.hom.app (op U) r) _).trans
      (congrArg (· • pullbackStalkSectionMap f φ G y U hy m)
        (stalkRingHom_germ_apply f φ y U hy r).symm))
private def pullbackStalkMap (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Module ↑(stalk S.obj (f y)) ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
      Module.compHom _ (stalkRingHom f φ y).hom
    ↑(stalk G.val.presheaf (f y)) →ₗ[↑(stalk S.obj (f y))]
      ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
  letI : Module ↑(stalk S.obj (f y)) ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
    Module.compHom _ (stalkRingHom f φ y).hom
  PresheafOfModules.stalkLiftCommRing (S := S.obj) (f y) G.val (pullbackStalkSectionMap f φ G y)
    (pullbackStalkSectionMap_res f φ G y) (pullbackStalkSectionMap_smul f φ G y)
private theorem pullbackStalkMap_germ (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (pullbackStalkMap f φ G y (germ G.val.presheaf U (f y) hy m) =
      germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m)) := by
  let _ : Module ↑(stalk S.obj (f y)) ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
    Module.compHom _ (stalkRingHom f φ y).hom
  unfold pullbackStalkMap; apply PresheafOfModules.stalkLiftCommRing_germ

/-- The canonical `R_y`-linear comparison map `R_y ⊗[S_{f(y)}] G_{f(y)} →ₗ[R_y] (f^* G)_y`. -/
def pullbackStalkComparison (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    ↑(stalk R.obj y) ⊗[↑(stalk S.obj (f y))] ↑(stalk G.val.presheaf (f y)) →ₗ[↑(stalk R.obj y)]
      ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
  letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  letI : Module ↑(stalk S.obj (f y)) ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
    Module.compHom _ (stalkRingHom f φ y).hom
  haveI : IsScalarTower ↑(stalk S.obj (f y)) ↑(stalk R.obj y)
      ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) := IsScalarTower.of_compHom _ _ _
  (pullbackStalkMap f φ G y).liftBaseChange ↑(stalk R.obj y)
@[simp] theorem pullbackStalkComparison_tmul_germ (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (a : ↑(stalk R.obj y)) (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (pullbackStalkComparison f φ G y (a ⊗ₜ[↑(stalk S.obj (f y))] germ G.val.presheaf U (f y) hy m) =
      a • germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m)) :=
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  congrArg (a • ·) (pullbackStalkMap_germ f φ G y U hy m)
theorem pullbackStalkComparison_one_tmul_germ (G : SheafOfModules.{u} (ringCatSheaf S))
    (y : Y) (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (pullbackStalkComparison f φ G y
        ((1 : ↑(stalk R.obj y)) ⊗ₜ[↑(stalk S.obj (f y))] germ G.val.presheaf U (f y) hy m) =
      germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m)) := by
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  exact (pullbackStalkComparison_tmul_germ f φ G y 1 U hy m).trans (one_smul _ _)
private def pullbackStalkYonedaEquiv (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (T : Type u) [AddCommGroup T] [Module ↑(stalk R.obj y) T] :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    (↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) →ₗ[↑(stalk R.obj y)] T) ≃
      (↑(stalk R.obj y) ⊗[↑(stalk S.obj (f y))] ↑(stalk G.val.presheaf (f y)) →ₗ[↑(stalk R.obj y)]
        T) :=
  letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  letI : Module ↑(stalk S.obj (f y)) T := Module.compHom T (stalkRingHom f φ y).hom
  haveI : IsScalarTower ↑(stalk S.obj (f y)) ↑(stalk R.obj y) T := IsScalarTower.of_compHom _ _ _
  (skyscraperCommRingHomEquiv R y T ((pullback.{u} φ).obj G)).symm.toEquiv
    |>.trans ((pullbackPushforwardAdjunction φ).homEquiv G (skyscraperCommRing R y T))
    |>.trans (Iso.homToEquiv (pushforwardSkyscraperCommRingIso S f R φ y (stalkRingHom f φ y)
      (stalkRingHom_germ_apply f φ y) T))
    |>.trans (skyscraperCommRingHomEquiv S (f y) T G).toEquiv
    |>.trans (LinearMap.liftBaseChangeEquiv ↑(stalk R.obj y)).toEquiv
private theorem pullbackStalkYonedaEquiv_apply (G : SheafOfModules.{u} (ringCatSheaf S))
    (y : Y) (T : Type u) [AddCommGroup T] [Module ↑(stalk R.obj y) T]
    (β : ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) →ₗ[↑(stalk R.obj y)] T) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    pullbackStalkYonedaEquiv f φ G y T β = β.comp (pullbackStalkComparison f φ G y) := by
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  let _ : Module ↑(stalk S.obj (f y)) T := Module.compHom T (stalkRingHom f φ y).hom
  have _ : IsScalarTower ↑(stalk S.obj (f y)) ↑(stalk R.obj y) T := IsScalarTower.of_compHom _ _ _
  refine TensorProduct.AlgebraTensorModule.ext fun a s ↦ ?_
  obtain ⟨U, hy, m, rfl⟩ := exists_germ_eq G.val.presheaf s
  let m' : G.val.obj (op U) := m
  let adj := pullbackPushforwardAdjunction φ
  let iso := pushforwardSkyscraperCommRingIso S f R φ y (stalkRingHom f φ y)
    (stalkRingHom_germ_apply f φ y) T
  let ψ := (skyscraperCommRingHomEquiv R y T ((pullback.{u} φ).obj G)).symm β
  let θ := adj.homEquiv G (skyscraperCommRing R y T) ψ ≫ iso.hom
  have happ : θ.val.app (op U) m' = iso.hom.val.app (op U)
      (ψ.val.app (op ((Opens.map f).obj U)) ((adj.unit.app G).val.app _ m')) := by
    simp only [θ, Adjunction.homEquiv_unit]; rfl
  have hθ := (skyscraperCommRingHomEquiv_germ S (f y) T θ U hy m').trans
    ((congrArg (skyscraperCommRingEval S (f y) T hy) happ).trans
      ((skyscraperCommRingEval_pushforwardSkyscraperCommRingIso_hom_app S f R φ y
        (stalkRingHom f φ y) (stalkRingHom_germ_apply f φ y) T U hy _).trans
        (skyscraperCommRingEval_skyscraperCommRingHomEquiv_symm_app R y T β
          ((Opens.map f).obj U) (Opens.mem_map.mpr hy) _)))
  exact (congrArg (a • ·) hθ).trans
    ((congrArg β (pullbackStalkComparison_tmul_germ f φ G y a U hy m')).trans (β.map_smul a _)).symm

/-- **Stalks of pulled-back sheaves of modules.** `R_y ⊗[S_{f(y)}] G_{f(y)} →ₗ[R_y] (f^* G)_y` is
bijective for every morphism of ringed spaces `(f, φ)` and sheaf of modules `G` (Tag 0098). -/
@[stacks 0098]
theorem pullbackStalkComparison_bijective (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    Function.Bijective (pullbackStalkComparison f φ G y) := by
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  set c := pullbackStalkComparison f φ G y
  set Src := ↑(stalk R.obj y) ⊗[↑(stalk S.obj (f y))] ↑(stalk G.val.presheaf (f y))
  set Tgt := ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y)
  let g := (pullbackStalkYonedaEquiv f φ G y Src).symm LinearMap.id
  have hg : g.comp c = LinearMap.id :=
    (pullbackStalkYonedaEquiv_apply f φ G y Src g).symm.trans
      ((pullbackStalkYonedaEquiv f φ G y Src).apply_symm_apply LinearMap.id)
  have hcg : c.comp g = LinearMap.id := by
    apply (pullbackStalkYonedaEquiv f φ G y Tgt).injective
    rw [pullbackStalkYonedaEquiv_apply, pullbackStalkYonedaEquiv_apply,
      LinearMap.comp_assoc, hg, LinearMap.comp_id, LinearMap.id_comp]
  exact ⟨Function.LeftInverse.injective (LinearMap.congr_fun hg),
    Function.RightInverse.surjective (LinearMap.congr_fun hcg)⟩

/-- Canonical `R_y`-linear equivalence `R_y ⊗[S_{f(y)}] G_{f(y)} ≃ₗ[R_y] (f^* G)_y` (Tag 0098). -/
@[stacks 0098] def pullbackStalkEquiv (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    ↑(stalk R.obj y) ⊗[↑(stalk S.obj (f y))] ↑(stalk G.val.presheaf (f y)) ≃ₗ[↑(stalk R.obj y)]
      ↑(stalk ((pullback.{u} φ).obj G).val.presheaf y) :=
  letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  LinearEquiv.ofBijective (pullbackStalkComparison f φ G y)
    (pullbackStalkComparison_bijective f φ G y)
@[simp] theorem pullbackStalkEquiv_apply (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    ∀ z, pullbackStalkEquiv f φ G y z = pullbackStalkComparison f φ G y z := fun _ ↦ (rfl)
theorem pullbackStalkEquiv_symm_germ_unit (G : SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    ((pullbackStalkEquiv f φ G y).symm
        (germ ((pullback.{u} φ).obj G).val.presheaf ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
          (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m)) =
      (1 : ↑(stalk R.obj y)) ⊗ₜ[↑(stalk S.obj (f y))] germ G.val.presheaf U (f y) hy m) :=
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  (pullbackStalkEquiv f φ G y).symm_apply_eq.mpr
    (pullbackStalkComparison_one_tmul_germ f φ G y U hy m).symm

/-- Value of `stalkMap β y ∘ pullbackStalkComparison f φ G y` on `a ⊗ germ(m)`. -/
theorem stalkMap_pullbackStalkComparison_tmul_germ (G : SheafOfModules.{u} (ringCatSheaf S))
    {H : SheafOfModules.{u} (ringCatSheaf R)} (β : (pullback.{u} φ).obj G ⟶ H) (y : Y)
    (a : ↑(stalk R.obj y)) (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (stalkMap β y (pullbackStalkComparison f φ G y
          (a ⊗ₜ[↑(stalk S.obj (f y))] germ G.val.presheaf U (f y) hy m)) =
      a • germ H.val.presheaf ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (β.val.app (op ((Opens.map f).obj U))
          (((pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m))) :=
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  (congrArg (stalkMap β y) (pullbackStalkComparison_tmul_germ f φ G y a U hy m)).trans
    ((map_smul (stalkMap β y) a _).trans
      (congrArg (a • ·) (stalkMap_germ β y ((Opens.map f).obj U) (Opens.mem_map.mpr hy) _)))

/-- Naturality of `pullbackStalkComparison` in `G`. -/
theorem pullbackStalkComparison_naturality {G G' : SheafOfModules.{u} (ringCatSheaf S)}
    (α : G ⟶ G') (y : Y) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    (stalkMap ((pullback.{u} φ).map α) y).comp (pullbackStalkComparison f φ G y) =
      (pullbackStalkComparison f φ G' y).comp ((stalkMap α (f y)).baseChange ↑(stalk R.obj y)) := by
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  let _ : Module ↑(stalk S.obj (f y)) ↑(stalk ((pullback.{u} φ).obj G').val.presheaf y) :=
    Module.compHom _ (algebraMap ↑(stalk S.obj (f y)) ↑(stalk R.obj y))
  have _ : IsScalarTower ↑(stalk S.obj (f y)) ↑(stalk R.obj y)
      ↑(stalk ((pullback.{u} φ).obj G').val.presheaf y) := IsScalarTower.of_compHom _ _ _
  refine TensorProduct.AlgebraTensorModule.ext fun a s ↦ ?_
  obtain ⟨U, hy, m, rfl⟩ := exists_germ_eq G.val.presheaf s
  let m' : G.val.obj (op U) := m
  have hn := congrArg (fun k ↦ k.val.app (op U) m')
    ((pullbackPushforwardAdjunction φ).unit.naturality α)
  exact (stalkMap_pullbackStalkComparison_tmul_germ f φ G ((pullback.{u} φ).map α) y a U hy
      m').trans
    ((congrArg (fun t ↦ a • germ ((pullback.{u} φ).obj G').val.presheaf ((Opens.map f).obj U) y
      (Opens.mem_map.mpr hy) t) hn.symm).trans
      ((congrArg (fun t ↦ pullbackStalkComparison f φ G' y (a ⊗ₜ t))
        (stalkMap_germ α (f y) U hy m')).trans
        (pullbackStalkComparison_tmul_germ f φ G' y a U hy (α.val.app (op U) m'))).symm)

/-- Naturality of `pullbackStalkEquiv` in `G`. -/
theorem pullbackStalkEquiv_naturality {G G' : SheafOfModules.{u} (ringCatSheaf S)}
    (α : G ⟶ G') (y : Y) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    (stalkMap ((pullback.{u} φ).map α) y).comp (pullbackStalkEquiv f φ G y).toLinearMap =
      (pullbackStalkEquiv f φ G' y).toLinearMap.comp
        ((stalkMap α (f y)).baseChange ↑(stalk R.obj y)) :=
  pullbackStalkComparison_naturality f φ α y

/-- Compatibility of `pullbackStalkComparison` at the unit sheaf with `pullbackObjUnitToUnit φ`. -/
theorem unitStalkEquiv_stalkMap_pullbackObjUnitToUnit_pullbackStalkComparison (y : Y) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    (unitStalkEquiv R y).toLinearMap.comp
        ((stalkMap (pullbackObjUnitToUnit φ) y).comp
          (pullbackStalkComparison f φ (unit (ringCatSheaf S)) y)) =
      (TensorProduct.AlgebraTensorModule.rid ↑(stalk S.obj (f y)) ↑(stalk R.obj y)
          ↑(stalk R.obj y)).toLinearMap.comp
        ((unitStalkEquiv S (f y)).toLinearMap.baseChange ↑(stalk R.obj y)) := by
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  refine TensorProduct.AlgebraTensorModule.ext fun a s ↦ ?_
  obtain ⟨U, hy, r, rfl⟩ := exists_germ_eq (unit (ringCatSheaf S)).val.presheaf s
  let r' : S.obj.obj (op U) := r
  have h₁ : (pullbackObjUnitToUnit φ).val.app (op ((Opens.map f).obj U))
      (((pullbackPushforwardAdjunction φ).unit.app (unit (ringCatSheaf S))).val.app (op U) r') =
      φ.hom.app (op U) r' :=
    congrArg (fun k ↦ k.val.app (op U) r')
      (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ)
  have hL := (congrArg (unitStalkEquiv R y)
      (stalkMap_pullbackStalkComparison_tmul_germ f φ (unit (ringCatSheaf S))
        (pullbackObjUnitToUnit φ) y a U hy r')).trans
    ((map_smul (unitStalkEquiv R y) a _).trans
      (congrArg (a • ·) ((congrArg (fun t ↦ unitStalkEquiv R y
        (germ (unit (ringCatSheaf R)).val.presheaf ((Opens.map f).obj U) y
          (Opens.mem_map.mpr hy) t)) h₁).trans
        (unitStalkEquiv_germ R y ((Opens.map f).obj U) (Opens.mem_map.mpr hy) _))))
  have hmid : a • germ R.obj ((Opens.map f).obj U) y (Opens.mem_map.mpr hy) (φ.hom.app (op U) r') =
      germ S.obj U (f y) hy r' • a := by
    rw [smul_eq_mul, Algebra.smul_def, mul_comm]
    exact congrArg (· * a) (stalkRingHom_germ_apply f φ y U hy r').symm
  exact hL.trans (hmid.trans (congrArg (· • a) (unitStalkEquiv_germ S (f y) U hy r')).symm)

/-- Pushforward of sheaves of modules along `g ≫ f` is a right adjoint whenever both factors are. -/
theorem isRightAdjoint_pushforward_comp {Z : TopCat.{u}} (g : Z ⟶ Y)
    {Q : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (ψ : ringCatSheaf R ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q))
    [(pushforward.{u} ψ).IsRightAdjoint] :
    (pushforward.{u} (compRingCatSheafHom f φ g ψ)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardComp.{u} φ ψ)

/-- Compatibility of `pullbackStalkComparison` with `pullbackComp` and `cancelBaseChange`. -/
theorem stalkMap_pullbackComp_inv_pullbackStalkComparison {Z : TopCat.{u}} (g : Z ⟶ Y)
    {Q : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (ψ : ringCatSheaf R ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q))
    [(pushforward.{u} ψ).IsRightAdjoint] (G : SheafOfModules.{u} (ringCatSheaf S)) (z : Z) :
    letI : (pushforward.{u} (compRingCatSheafHom f φ g ψ)).IsRightAdjoint :=
      isRightAdjoint_pushforward_comp f φ g ψ
    letI : Algebra ↑(stalk S.obj (f (g z))) ↑(stalk R.obj (g z)) :=
      (stalkRingHom f φ (g z)).hom.toAlgebra
    letI : Algebra ↑(stalk R.obj (g z)) ↑(stalk Q.obj z) := (stalkRingHom g ψ z).hom.toAlgebra
    letI : Algebra ↑(stalk S.obj (f (g z))) ↑(stalk Q.obj z) :=
      (stalkRingHom (g ≫ f) (compRingCatSheafHom f φ g ψ) z).hom.toAlgebra
    haveI : IsScalarTower ↑(stalk S.obj (f (g z))) ↑(stalk R.obj (g z)) ↑(stalk Q.obj z) :=
      IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (stalkRingHom_comp f φ g ψ z))
    (stalkMap ((pullbackComp φ ψ).inv.app G) z).comp
        (pullbackStalkComparison (g ≫ f) (compRingCatSheafHom f φ g ψ) G z) =
      (pullbackStalkComparison g ψ ((pullback.{u} φ).obj G) z).comp
        (((pullbackStalkComparison f φ G (g z)).baseChange ↑(stalk Q.obj z)).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            ↑(stalk S.obj (f (g z))) ↑(stalk R.obj (g z)) ↑(stalk Q.obj z) ↑(stalk Q.obj z)
            ↑(stalk G.val.presheaf (f (g z)))).symm.toLinearMap) := by
  let _ : (pushforward.{u} (compRingCatSheafHom f φ g ψ)).IsRightAdjoint :=
    isRightAdjoint_pushforward_comp f φ g ψ
  let _ : Algebra ↑(stalk S.obj (f (g z))) ↑(stalk R.obj (g z)) :=
    (stalkRingHom f φ (g z)).hom.toAlgebra
  let _ : Algebra ↑(stalk R.obj (g z)) ↑(stalk Q.obj z) := (stalkRingHom g ψ z).hom.toAlgebra
  let _ : Algebra ↑(stalk S.obj (f (g z))) ↑(stalk Q.obj z) :=
    (stalkRingHom (g ≫ f) (compRingCatSheafHom f φ g ψ) z).hom.toAlgebra
  have _ : IsScalarTower ↑(stalk S.obj (f (g z))) ↑(stalk R.obj (g z)) ↑(stalk Q.obj z) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (stalkRingHom_comp f φ g ψ z))
  let Cod := ↑(stalk ((pullback.{u} φ ⋙ pullback.{u} ψ).obj G).val.presheaf z)
  let _ : Module ↑(stalk S.obj (f (g z))) Cod :=
    Module.compHom Cod (algebraMap ↑(stalk S.obj (f (g z))) ↑(stalk Q.obj z))
  have _ : IsScalarTower ↑(stalk S.obj (f (g z))) ↑(stalk Q.obj z) Cod :=
    IsScalarTower.of_compHom _ _ _
  refine TensorProduct.AlgebraTensorModule.ext (R := ↑(stalk S.obj (f (g z))))
    (N := ↑(stalk G.val.presheaf (f (g z)))) fun q s ↦ ?_
  obtain ⟨U, hz, m, rfl⟩ := exists_germ_eq G.val.presheaf s
  let m' : G.val.obj (op U) := m
  have hc := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction φ).comp (pullbackPushforwardAdjunction ψ))
    (pullbackPushforwardAdjunction _) (pullbackComp φ ψ).inv G
  rw [conjugateEquiv_pullbackComp_inv] at hc
  have happ := (congrArg (fun k ↦ k.val.app (op U) m') hc).symm
  have hL := stalkMap_pullbackStalkComparison_tmul_germ (g ≫ f) (compRingCatSheafHom f φ g ψ) G
    ((pullbackComp φ ψ).inv.app G) z q U hz m'
  have hR := (congrArg (fun t ↦ pullbackStalkComparison g ψ ((pullback.{u} φ).obj G) z (q ⊗ₜ t))
      (pullbackStalkComparison_one_tmul_germ f φ G (g z) U hz m')).trans
    (pullbackStalkComparison_tmul_germ g ψ ((pullback.{u} φ).obj G) z q ((Opens.map f).obj U)
      (Opens.mem_map.mpr hz) _)
  let P₂ := ((pullback.{u} ψ).obj ((pullback.{u} φ).obj G)).val.presheaf
  exact hL.trans ((congrArg (fun t ↦ q • germ P₂ ((Opens.map g).obj ((Opens.map f).obj U)) z
    (Opens.mem_map.mpr (Opens.mem_map.mpr hz)) t) happ).trans hR.symm)
end PullbackStalk
end SheafOfModules
end
