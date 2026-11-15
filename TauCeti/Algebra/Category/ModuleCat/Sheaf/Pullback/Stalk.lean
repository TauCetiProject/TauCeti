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

Let `f : Y ⟶ X` be a continuous map of topological spaces, `S` and `R` sheaves of commutative rings
on `X` and `Y`, and `φ : S ⟶ f_* R` a morphism of the underlying sheaves of rings. At every point
`y : Y`, `(f, φ)` induces a commutative-ring homomorphism on stalks
`TauCeti.SheafOfModules.stalkRingHom f φ y : S_{f(y)} ⟶ R_y`.

For every sheaf of `S`-modules `G`, this file constructs the canonical `R_y`-linear comparison map
`TauCeti.SheafOfModules.pullbackStalkComparison f φ G y` from `R_y ⊗[S_{f(y)}] G_{f(y)}` to
`(f^* G)_y`, characterized on pure tensors of germs by sending `a ⊗ germ(m)` to `a` acting on the
germ of the pulled-back section `η_G(m)`, and proves that it is bijective without finiteness or
quasi-coherence assumptions (`TauCeti.SheafOfModules.pullbackStalkComparison_bijective`), yielding
the linear equivalence `TauCeti.SheafOfModules.pullbackStalkEquiv`.

Bijectivity is proved by Yoneda through skyscraper sheaves of modules
(`TauCeti.SheafOfModules.skyscraperCommRing`): for every `R_y`-module `T`, precomposition with
`pullbackStalkComparison f φ G y` coincides with the chain of bijections
`Hom_{R_y}((f^* G)_y, T) ≃ Hom_R(f^* G, i_{y,*} T) ≃ Hom_S(G, f_* i_{y,*} T)`
`≃ Hom_S(G, i_{f(y),*} T) ≃ Hom_{S_{f(y)}}(G_{f(y)}, T) ≃ Hom_{R_y}(R_y ⊗[S_{f(y)}] G_{f(y)}, T)`.

We also prove naturality in `G`, compatibility with the unit map
`SheafOfModules.pullbackObjUnitToUnit φ` via `TauCeti.SheafOfModules.unitStalkEquiv`, and
compatibility with composition `SheafOfModules.pullbackComp` via
`TensorProduct.AlgebraTensorModule.cancelBaseChange`.

## Main declarations

* `TauCeti.SheafOfModules.stalkRingHom`: the ring homomorphism `S_{f(y)} ⟶ R_y` on stalks;
* `TauCeti.SheafOfModules.unitStalkEquiv`: the `S_x`-linear identification of the stalk of the unit
  sheaf of modules `SheafOfModules.unit (ringCatSheaf S)` at `x` with `S_x`;
* `TauCeti.SheafOfModules.pullbackStalkComparison` and
  `TauCeti.SheafOfModules.pullbackStalkComparison_bijective`: the comparison
  `R_y ⊗[S_{f(y)}] G_{f(y)} →ₗ[R_y] (f^* G)_y` and its bijectivity;
* `TauCeti.SheafOfModules.pullbackStalkEquiv`: the resulting `R_y`-linear equivalence;
* `TauCeti.SheafOfModules.pullbackStalkComparison_naturality` and
  `TauCeti.SheafOfModules.pullbackStalkEquiv_naturality`: naturality in `G`;
* `TauCeti.SheafOfModules.unitStalkEquiv_stalkMap_pullbackObjUnitToUnit_pullbackStalkComparison`:
  compatibility with the unit identification;
* `TauCeti.SheafOfModules.stalkMap_pullbackComp_inv_pullbackStalkComparison`: compatibility with
  composition of pullbacks.

## References

* [The Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098).
-/

public section

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace TauCeti.SheafOfModules

open _root_.SheafOfModules

section StalkRingHom

variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf R))

/-- The ring homomorphism `S_{f(y)} ⟶ R_y` on stalks induced by a continuous map `f : Y ⟶ X` and a
morphism of underlying sheaves of rings `φ : S ⟶ f_* R`. -/
def stalkRingHom (y : Y) :
    TopCat.Presheaf.stalk S.obj (f y) ⟶ TopCat.Presheaf.stalk R.obj y :=
  let ψ₀ := commRingCatHom.{u, u, u, u, u} φ
  let ψ : (S.obj : X.Presheaf CommRingCat.{u}) ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} f).obj R.obj := ψ₀
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f y)).map ψ ≫
    TopCat.Presheaf.stalkPushforward CommRingCat.{u} f R.obj y

@[reassoc (attr := simp)]
theorem stalkRingHom_germ (y : Y) (U : Opens X) (hy : f y ∈ U) :
    TopCat.Presheaf.germ S.obj U (f y) hy ≫ stalkRingHom f φ y =
      (commRingCatHom.{u, u, u, u, u} φ).app (op U) ≫
        TopCat.Presheaf.germ R.obj ((Opens.map f).obj U) y (Opens.mem_map.mpr hy) := by
  rw [stalkRingHom]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]

@[simp]
theorem stalkRingHom_germ_apply (y : Y) (U : Opens X) (hy : f y ∈ U) (r : S.obj.obj (op U)) :
    stalkRingHom f φ y (TopCat.Presheaf.germ S.obj U (f y) hy r) =
      TopCat.Presheaf.germ R.obj ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (φ.hom.app (op U) r) :=
  ConcreteCategory.congr_hom (stalkRingHom_germ f φ y U hy) r

@[simp]
theorem stalkRingHom_id (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X) :
    stalkRingHom (𝟙 X) (𝟙 (ringCatSheaf S)) x = 𝟙 (TopCat.Presheaf.stalk S.obj x) := by
  refine TopCat.Presheaf.stalk_hom_ext S.obj fun U hx ↦ ?_
  ext r
  exact stalkRingHom_germ_apply (𝟙 X) (𝟙 (ringCatSheaf S)) x U hx r

/-- The composite morphism of underlying sheaves of rings along `g ≫ f`. Its body is exposed so
that on schemes `(f ≫ g).toRingCatSheafHom` is definitionally this composite. -/
@[expose]
def compRingCatSheafHom {Z : TopCat.{u}} (g : Z ⟶ Y)
    {Q : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (ψ : ringCatSheaf R ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q)) :
    ringCatSheaf S ⟶
      ((Opens.map (g ≫ f)).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj (ringCatSheaf Q) :=
  let θ := φ ≫
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ
  θ

theorem stalkRingHom_comp {Z : TopCat.{u}} (g : Z ⟶ Y)
    {Q : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (ψ : ringCatSheaf R ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q))
    (z : Z) :
    stalkRingHom (g ≫ f) (compRingCatSheafHom f φ g ψ) z =
      stalkRingHom f φ (g z) ≫ stalkRingHom g ψ z := by
  refine TopCat.Presheaf.stalk_hom_ext S.obj fun U hz ↦ ?_
  ext r
  have h₁ := stalkRingHom_germ_apply (g ≫ f) (compRingCatSheafHom f φ g ψ) z U hz r
  have h₂ := stalkRingHom_germ_apply f φ (g z) U hz r
  have h₃ := stalkRingHom_germ_apply g ψ z ((Opens.map f).obj U) (Opens.mem_map.mpr hz)
    (φ.hom.app (op U) r)
  exact h₁.trans (h₃.symm.trans (congrArg (stalkRingHom g ψ z) h₂.symm))

end StalkRingHom

section UnitStalk

variable {X : TopCat.{u}} (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)

/-- The canonical `S_x`-linear map from the stalk of the unit sheaf of modules
`SheafOfModules.unit (ringCatSheaf S)` at `x` to the ring stalk `S_x`. -/
def unitStalkComparison :
    ↑(TopCat.Presheaf.stalk (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf x) →ₗ[
      ↑(TopCat.Presheaf.stalk S.obj x)]
      ↑(TopCat.Presheaf.stalk S.obj x) :=
  let Q : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
    (_root_.SheafOfModules.unit (ringCatSheaf S)).val
  Q.stalkLiftCommRing (S := S.obj) x
    (fun U hx ↦ (TopCat.Presheaf.germ S.obj U x hx).hom.toAddMonoidHom)
    (fun {_ _} i hx r ↦ TopCat.Presheaf.germ_res_apply S.obj i x hx r)
    (fun U hx r m ↦ map_mul (TopCat.Presheaf.germ S.obj U x hx).hom r m)

@[simp]
theorem unitStalkComparison_germ (U : Opens X) (hx : x ∈ U) (r : S.obj.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (unitStalkComparison S x
        (TopCat.Presheaf.germ (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf U x hx r) =
      TopCat.Presheaf.germ S.obj U x hx r) := by
  let Q : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
    (_root_.SheafOfModules.unit (ringCatSheaf S)).val
  exact Q.stalkLiftCommRing_germ (S := S.obj) x
    (fun U hx ↦ (TopCat.Presheaf.germ S.obj U x hx).hom.toAddMonoidHom)
    (fun {_ _} i hx r ↦ TopCat.Presheaf.germ_res_apply S.obj i x hx r)
    (fun U hx r m ↦ map_mul (TopCat.Presheaf.germ S.obj U x hx).hom r m)
    U hx r

/-- The canonical `S_x`-linear equivalence identifying the stalk of the unit sheaf of modules
`SheafOfModules.unit (ringCatSheaf S)` at `x` with the ring stalk `S_x`. -/
def unitStalkEquiv :
    ↑(TopCat.Presheaf.stalk (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf x) ≃ₗ[
      ↑(TopCat.Presheaf.stalk S.obj x)]
      ↑(TopCat.Presheaf.stalk S.obj x) :=
  LinearEquiv.ofLinearMap
    (unitStalkComparison S x)
    (LinearMap.toSpanSingleton ↑(TopCat.Presheaf.stalk S.obj x) _
      (TopCat.Presheaf.germ (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf
        ⊤ x (Opens.mem_top x) (1 : S.obj.obj (op ⊤))))
    (LinearMap.ext fun a ↦ by
      simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply,
        map_smul]
      have h₁ := unitStalkComparison_germ S x ⊤ (Opens.mem_top x) (1 : S.obj.obj (op ⊤))
      erw [h₁]
      rw [map_one (TopCat.Presheaf.germ S.obj ⊤ x (Opens.mem_top x)).hom, smul_eq_mul, mul_one])
    (LinearMap.ext fun s ↦ by
      obtain ⟨U, hx, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq
        (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf s
      let r' : S.obj.obj (op U) := r
      let Q : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
        (_root_.SheafOfModules.unit (ringCatSheaf S)).val
      simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply]
      have h₁ := unitStalkComparison_germ S x U hx r'
      erw [h₁]
      have hres := TopCat.Presheaf.germ_res_apply
        (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf (homOfLE (le_top : U ≤ ⊤))
        x hx (1 : S.obj.obj (op ⊤))
      rw [← hres]
      -- On sections of the unit sheaf of modules, scalar multiplication is multiplication in `S`,
      -- and the restriction map of `S` preserves `1`.
      exact (Q.germ_smul (R := S.obj) x U hx r' _).symm.trans
        (congrArg
          (TopCat.Presheaf.germ (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf U x hx)
          ((congrArg (r' * ·) (map_one (S.obj.map (homOfLE (le_top : U ≤ ⊤)).op).hom)).trans
            (mul_one r'))))

@[simp]
theorem unitStalkEquiv_apply
    (s : ↑(TopCat.Presheaf.stalk (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf x)) :
    unitStalkEquiv S x s = unitStalkComparison S x s :=
  (rfl)

theorem unitStalkEquiv_germ (U : Opens X) (hx : x ∈ U) (r : S.obj.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (unitStalkEquiv S x
        (TopCat.Presheaf.germ (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf U x hx r) =
      TopCat.Presheaf.germ S.obj U x hx r) :=
  unitStalkComparison_germ S x U hx r

@[simp]
theorem unitStalkEquiv_symm_apply (a : ↑(TopCat.Presheaf.stalk S.obj x)) :
    (unitStalkEquiv S x).symm a =
      a • TopCat.Presheaf.germ (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf
        ⊤ x (Opens.mem_top x) (1 : S.obj.obj (op ⊤)) :=
  (rfl)

end UnitStalk

section PullbackStalk

variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf R))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

private def pullbackStalkSectionMap (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (U : Opens X) (hy : f y ∈ U) :
    (G.val.obj (op U) : Type u) →+
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
  (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf
    ((Opens.map f).obj U) y hy).hom.comp
      (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app
        (op U)).hom.toAddMonoidHom

private theorem pullbackStalkSectionMap_res (G : _root_.SheafOfModules.{u} (ringCatSheaf S))
    (y : Y) {U V : Opens X} (i : U ⟶ V) (hy : f y ∈ U) (m : G.val.obj (op V)) :
    pullbackStalkSectionMap f φ G y U hy (G.val.map i.op m) =
      pullbackStalkSectionMap f φ G y V (i.le hy) m := by
  have hn := PresheafOfModules.naturality_apply
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val i.op m
  have hg := TopCat.Presheaf.germ_res_apply
    ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf ((Opens.map f).map i) y hy
    (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app (op V) m)
  exact (congrArg
    (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf
      ((Opens.map f).obj U) y hy) hn).trans hg

private theorem pullbackStalkSectionMap_smul (G : _root_.SheafOfModules.{u} (ringCatSheaf S))
    (y : Y) (U : Opens X) (hy : f y ∈ U) (r : S.obj.obj (op U)) (m : G.val.obj (op U)) :
    letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y))
        ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
      Module.compHom _ (stalkRingHom f φ y).hom
    pullbackStalkSectionMap f φ G y U hy (r • m) =
      TopCat.Presheaf.germ S.obj U (f y) hy r • pullbackStalkSectionMap f φ G y U hy m := by
  let _ : Module ↑(TopCat.Presheaf.stalk S.obj (f y))
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
    Module.compHom _ (stalkRingHom f φ y).hom
  let P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
    ((_root_.SheafOfModules.pullback.{u} φ).obj G).val
  have h₁ := congrArg
    (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf
      ((Opens.map f).obj U) y hy)
    ((((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app
      (op U)).hom.map_smul r m)
  have h₂ := P.germ_smul (R := R.obj) y ((Opens.map f).obj U) hy (φ.hom.app (op U) r)
    (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m)
  have h₃ := congrArg (· • pullbackStalkSectionMap f φ G y U hy m)
    (stalkRingHom_germ_apply f φ y U hy r).symm
  exact h₁.trans (h₂.trans h₃)

private def pullbackStalkMapAux (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y))
        ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
      Module.compHom _ (stalkRingHom f φ y).hom
    ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) →ₗ[↑(TopCat.Presheaf.stalk S.obj (f y))]
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
  letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y))
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
    Module.compHom _ (stalkRingHom f φ y).hom
  let GS : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat.{u}) := G.val
  GS.stalkLiftCommRing (S := S.obj) (f y) (pullbackStalkSectionMap f φ G y)
    (pullbackStalkSectionMap_res f φ G y) (pullbackStalkSectionMap_smul f φ G y)

/-- The canonical `R_y`-linear comparison map
`R_y ⊗[S_{f(y)}] G_{f(y)} →ₗ[R_y] (f^* G)_y` for the stalk of a pulled-back sheaf of modules,
where `R_y` is an `S_{f(y)}`-algebra via `stalkRingHom f φ y`. -/
def pullbackStalkComparison (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    ↑(TopCat.Presheaf.stalk R.obj y) ⊗[↑(TopCat.Presheaf.stalk S.obj (f y))]
        ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) →ₗ[↑(TopCat.Presheaf.stalk R.obj y)]
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
  letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y))
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
    Module.compHom _ (stalkRingHom f φ y).hom
  haveI : IsScalarTower ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y)
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
    IsScalarTower.of_compHom _ _ _
  (pullbackStalkMapAux f φ G y).liftBaseChange ↑(TopCat.Presheaf.stalk R.obj y)

@[simp]
theorem pullbackStalkComparison_tmul_germ (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (a : ↑(TopCat.Presheaf.stalk R.obj y)) (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (pullbackStalkComparison f φ G y
        (a ⊗ₜ[↑(TopCat.Presheaf.stalk S.obj (f y))]
          TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      a • TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf
        ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app (op U) m)) :=
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  let _ : Module ↑(TopCat.Presheaf.stalk S.obj (f y))
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
    Module.compHom _ (stalkRingHom f φ y).hom
  let GS : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat.{u}) := G.val
  congrArg (a • ·)
    (GS.stalkLiftCommRing_germ (S := S.obj) (f y) (pullbackStalkSectionMap f φ G y)
      (pullbackStalkSectionMap_res f φ G y) (pullbackStalkSectionMap_smul f φ G y) U hy m)

theorem pullbackStalkComparison_one_tmul_germ (G : _root_.SheafOfModules.{u} (ringCatSheaf S))
    (y : Y) (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (pullbackStalkComparison f φ G y
        ((1 : ↑(TopCat.Presheaf.stalk R.obj y)) ⊗ₜ[↑(TopCat.Presheaf.stalk S.obj (f y))]
          TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf
        ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app
          (op U) m)) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  exact (pullbackStalkComparison_tmul_germ f φ G y 1 U hy m).trans (one_smul _ _)

private theorem algebraTensor_ext {R₀ A₀ N₀ P₀ : Type*} [CommRing R₀] [CommRing A₀]
    [Algebra R₀ A₀] [AddCommGroup N₀] [Module R₀ N₀] [AddCommGroup P₀] [Module A₀ P₀]
    {g h : A₀ ⊗[R₀] N₀ →ₗ[A₀] P₀} (H : ∀ a n, g (a ⊗ₜ n) = h (a ⊗ₜ n)) : g = h := by
  let _ : Module R₀ P₀ := Module.compHom P₀ (algebraMap R₀ A₀)
  have _ : IsScalarTower R₀ A₀ P₀ := IsScalarTower.of_compHom R₀ A₀ P₀
  exact TensorProduct.AlgebraTensorModule.ext H

/-- Auxiliary Yoneda bijection identifying `R_y`-linear maps out of `(f^* G)_y` into any
`R_y`-module `T` with `R_y`-linear maps out of `R_y ⊗[S_{f(y)}] G_{f(y)}` into `T`, via skyscraper
sheaves and the pullback--pushforward adjunction. -/
private def pullbackStalkYonedaEquiv (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (T : Type u) [AddCommGroup T] [Module ↑(TopCat.Presheaf.stalk R.obj y) T] :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    (↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) →ₗ[
        ↑(TopCat.Presheaf.stalk R.obj y)] T) ≃
      (↑(TopCat.Presheaf.stalk R.obj y) ⊗[↑(TopCat.Presheaf.stalk S.obj (f y))]
          ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) →ₗ[↑(TopCat.Presheaf.stalk R.obj y)] T) :=
  letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  letI : Module ↑(TopCat.Presheaf.stalk S.obj (f y)) T :=
    Module.compHom T (stalkRingHom f φ y).hom
  haveI : IsScalarTower ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) T :=
    IsScalarTower.of_compHom _ _ _
  (skyscraperCommRingHomEquiv R y T ((_root_.SheafOfModules.pullback.{u} φ).obj G)).symm.toEquiv
    |>.trans ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv G
      (skyscraperCommRing R y T))
    |>.trans (Iso.homToEquiv (pushforwardSkyscraperCommRingIso S f R φ y (stalkRingHom f φ y)
      (stalkRingHom_germ_apply f φ y) T))
    |>.trans (skyscraperCommRingHomEquiv S (f y) T G).toEquiv
    |>.trans (LinearMap.liftBaseChangeEquiv ↑(TopCat.Presheaf.stalk R.obj y)).toEquiv

private theorem pullbackStalkYonedaEquiv_apply (G : _root_.SheafOfModules.{u} (ringCatSheaf S))
    (y : Y) (T : Type u) [AddCommGroup T] [Module ↑(TopCat.Presheaf.stalk R.obj y) T]
    (β : ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) →ₗ[
      ↑(TopCat.Presheaf.stalk R.obj y)] T) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    pullbackStalkYonedaEquiv f φ G y T β = β.comp (pullbackStalkComparison f φ G y) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  let _ : Module ↑(TopCat.Presheaf.stalk S.obj (f y)) T :=
    Module.compHom T (stalkRingHom f φ y).hom
  have _ : IsScalarTower ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) T :=
    IsScalarTower.of_compHom _ _ _
  apply algebraTensor_ext
  intro a s
  obtain ⟨U, hy, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf s
  let m' : G.val.obj (op U) := m
  let adj := _root_.SheafOfModules.pullbackPushforwardAdjunction φ
  let iso := pushforwardSkyscraperCommRingIso S f R φ y (stalkRingHom f φ y)
    (stalkRingHom_germ_apply f φ y) T
  let ψ := (skyscraperCommRingHomEquiv R y T ((_root_.SheafOfModules.pullback.{u} φ).obj G)).symm β
  let θ := adj.homEquiv G (skyscraperCommRing R y T) ψ ≫ iso.hom
  have happ : θ.val.app (op U) m' =
      iso.hom.val.app (op U)
        (ψ.val.app (op ((Opens.map f).obj U)) ((adj.unit.app G).val.app _ m')) := by
    simp only [θ, Adjunction.homEquiv_unit]; rfl
  have hθ : skyscraperCommRingHomEquiv S (f y) T G θ
      (TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      β (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf
        ((Opens.map f).obj U) y (Opens.mem_map.mpr hy) ((adj.unit.app G).val.app (op U) m')) :=
    (skyscraperCommRingHomEquiv_germ S (f y) T θ U hy m').trans
      ((congrArg (skyscraperCommRingEval S (f y) T hy) happ).trans
        ((skyscraperCommRingEval_pushforwardSkyscraperCommRingIso_hom_app S f R φ y
          (stalkRingHom f φ y) (stalkRingHom_germ_apply f φ y) T U hy _).trans
          (skyscraperCommRingEval_skyscraperCommRingHomEquiv_symm_app R y T β
            ((Opens.map f).obj U) (Opens.mem_map.mpr hy) _)))
  have hR : (β.comp (pullbackStalkComparison f φ G y))
      (a ⊗ₜ TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) =
      a • β (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf
        ((Opens.map f).obj U) y (Opens.mem_map.mpr hy) ((adj.unit.app G).val.app (op U) m')) :=
    (congrArg β (pullbackStalkComparison_tmul_germ f φ G y a U hy m')).trans (β.map_smul a _)
  exact (congrArg (a • ·) hθ).trans hR.symm

/-- **Stalks of pulled-back sheaves of modules.** For every morphism of ringed spaces `(f, φ)` and
every sheaf of modules `G`, the canonical comparison
`R_y ⊗[S_{f(y)}] G_{f(y)} →ₗ[R_y] (f^* G)_y` is bijective (Stacks Project, Tag 0098). -/
@[stacks 0098]
theorem pullbackStalkComparison_bijective (G : _root_.SheafOfModules.{u} (ringCatSheaf S))
    (y : Y) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    Function.Bijective (pullbackStalkComparison f φ G y) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  set c := pullbackStalkComparison f φ G y
  set Src := ↑(TopCat.Presheaf.stalk R.obj y) ⊗[↑(TopCat.Presheaf.stalk S.obj (f y))]
    ↑(TopCat.Presheaf.stalk G.val.presheaf (f y))
  set Tgt := ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y)
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

/-- The canonical `R_y`-linear equivalence `R_y ⊗[S_{f(y)}] G_{f(y)} ≃ₗ[R_y] (f^* G)_y` identifying
the stalk of a pulled-back sheaf of modules at `y` with the base change of the stalk at `f y` along
`stalkRingHom f φ y` (Stacks Project, Tag 0098). -/
@[stacks 0098]
def pullbackStalkEquiv (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    ↑(TopCat.Presheaf.stalk R.obj y) ⊗[↑(TopCat.Presheaf.stalk S.obj (f y))]
        ↑(TopCat.Presheaf.stalk G.val.presheaf (f y)) ≃ₗ[↑(TopCat.Presheaf.stalk R.obj y)]
      ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf y) :=
  letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  LinearEquiv.ofBijective (pullbackStalkComparison f φ G y)
    (pullbackStalkComparison_bijective f φ G y)

@[simp]
theorem pullbackStalkEquiv_apply (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    ∀ z, pullbackStalkEquiv f φ G y z = pullbackStalkComparison f φ G y z :=
  fun _ ↦ (rfl)

theorem pullbackStalkEquiv_symm_germ_unit (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    ((pullbackStalkEquiv f φ G y).symm
        (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G).val.presheaf
          ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
          (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app
            (op U) m)) =
      (1 : ↑(TopCat.Presheaf.stalk R.obj y)) ⊗ₜ[↑(TopCat.Presheaf.stalk S.obj (f y))]
        TopCat.Presheaf.germ G.val.presheaf U (f y) hy m) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  exact (pullbackStalkEquiv f φ G y).symm_apply_eq.mpr
    (pullbackStalkComparison_one_tmul_germ f φ G y U hy m).symm

/-- Value of `SheafOfModules.stalkMap β y ∘ pullbackStalkComparison f φ G y` on a pure tensor of a
stalk element and a germ. -/
theorem stalkMap_pullbackStalkComparison_tmul_germ
    (G : _root_.SheafOfModules.{u} (ringCatSheaf S))
    {H : _root_.SheafOfModules.{u} (ringCatSheaf R)}
    (β : (_root_.SheafOfModules.pullback.{u} φ).obj G ⟶ H) (y : Y)
    (a : ↑(TopCat.Presheaf.stalk R.obj y)) (U : Opens X) (hy : f y ∈ U) (m : G.val.obj (op U)) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (_root_.SheafOfModules.stalkMap β y
        (pullbackStalkComparison f φ G y
          (a ⊗ₜ[↑(TopCat.Presheaf.stalk S.obj (f y))]
            TopCat.Presheaf.germ G.val.presheaf U (f y) hy m)) =
      a • TopCat.Presheaf.germ H.val.presheaf ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (β.val.app (op ((Opens.map f).obj U))
          (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G).val.app
            (op U) m))) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  exact (congrArg (_root_.SheafOfModules.stalkMap β y)
    (pullbackStalkComparison_tmul_germ f φ G y a U hy m)).trans
    ((map_smul (_root_.SheafOfModules.stalkMap β y) a _).trans
      (congrArg (a • ·)
        (_root_.SheafOfModules.stalkMap_germ β y ((Opens.map f).obj U) (Opens.mem_map.mpr hy) _)))

/-- Naturality of `pullbackStalkComparison` in the sheaf of modules `G`. -/
theorem pullbackStalkComparison_naturality
    {G G' : _root_.SheafOfModules.{u} (ringCatSheaf S)} (α : G ⟶ G') (y : Y) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    (_root_.SheafOfModules.stalkMap ((_root_.SheafOfModules.pullback.{u} φ).map α) y).comp
        (pullbackStalkComparison f φ G y) =
      (pullbackStalkComparison f φ G' y).comp
        ((_root_.SheafOfModules.stalkMap α (f y)).baseChange
          ↑(TopCat.Presheaf.stalk R.obj y)) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  apply algebraTensor_ext
  intro a s
  obtain ⟨U, hy, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf s
  let m' : G.val.obj (op U) := m
  have hL := stalkMap_pullbackStalkComparison_tmul_germ f φ G
    ((_root_.SheafOfModules.pullback.{u} φ).map α) y a U hy m'
  have hR : pullbackStalkComparison f φ G' y
      ((_root_.SheafOfModules.stalkMap α (f y)).baseChange ↑(TopCat.Presheaf.stalk R.obj y)
        (a ⊗ₜ TopCat.Presheaf.germ G.val.presheaf U (f y) hy m)) =
      a • TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback.{u} φ).obj G').val.presheaf
        ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app G').val.app (op U)
          (α.val.app (op U) m')) :=
    (congrArg (fun t ↦ pullbackStalkComparison f φ G' y (a ⊗ₜ t))
      (_root_.SheafOfModules.stalkMap_germ α (f y) U hy m')).trans
      (pullbackStalkComparison_tmul_germ f φ G' y a U hy (α.val.app (op U) m'))
  have hn := congrArg (fun k ↦ k.val.app (op U) m')
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.naturality α)
  exact hL.trans
    ((congrArg (fun t ↦ a • TopCat.Presheaf.germ
      ((_root_.SheafOfModules.pullback.{u} φ).obj G').val.presheaf ((Opens.map f).obj U) y
      (Opens.mem_map.mpr hy) t) hn.symm).trans hR.symm)

/-- Naturality of `pullbackStalkEquiv` in the sheaf of modules `G`. -/
theorem pullbackStalkEquiv_naturality
    {G G' : _root_.SheafOfModules.{u} (ringCatSheaf S)} (α : G ⟶ G') (y : Y) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    (_root_.SheafOfModules.stalkMap ((_root_.SheafOfModules.pullback.{u} φ).map α) y).comp
        (pullbackStalkEquiv f φ G y).toLinearMap =
      (pullbackStalkEquiv f φ G' y).toLinearMap.comp
        ((_root_.SheafOfModules.stalkMap α (f y)).baseChange
          ↑(TopCat.Presheaf.stalk R.obj y)) :=
  pullbackStalkComparison_naturality f φ α y

/-- Compatibility of `pullbackStalkComparison` at the unit sheaf of modules with
`SheafOfModules.pullbackObjUnitToUnit φ` and `unitStalkEquiv`: on `R_y ⊗[S_{f(y)}] S_{f(y)}`, the
composite sends `a ⊗ u` to `unitStalkEquiv S (f y) u • a`
(via `TensorProduct.AlgebraTensorModule.rid`). -/
theorem unitStalkEquiv_stalkMap_pullbackObjUnitToUnit_pullbackStalkComparison (y : Y) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    (unitStalkEquiv R y).toLinearMap.comp
        ((_root_.SheafOfModules.stalkMap (_root_.SheafOfModules.pullbackObjUnitToUnit φ) y).comp
          (pullbackStalkComparison f φ (_root_.SheafOfModules.unit (ringCatSheaf S)) y)) =
      (TensorProduct.AlgebraTensorModule.rid ↑(TopCat.Presheaf.stalk S.obj (f y))
          ↑(TopCat.Presheaf.stalk R.obj y) ↑(TopCat.Presheaf.stalk R.obj y)).toLinearMap.comp
        ((unitStalkEquiv S (f y)).toLinearMap.baseChange ↑(TopCat.Presheaf.stalk R.obj y)) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  apply algebraTensor_ext
  intro a s
  obtain ⟨U, hy, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf s
  let r' : S.obj.obj (op U) := r
  have h₁ : ((_root_.SheafOfModules.pullbackObjUnitToUnit φ).val.app (op ((Opens.map f).obj U)))
      (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app
        (_root_.SheafOfModules.unit (ringCatSheaf S))).val.app (op U) r') =
      φ.hom.app (op U) r' :=
    congrArg (fun k ↦ k.val.app (op U) r')
      (_root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ)
  have hL : unitStalkEquiv R y
      (_root_.SheafOfModules.stalkMap (_root_.SheafOfModules.pullbackObjUnitToUnit φ) y
        (pullbackStalkComparison f φ (_root_.SheafOfModules.unit (ringCatSheaf S)) y
          (a ⊗ₜ TopCat.Presheaf.germ (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf
            U (f y) hy r))) =
      a • TopCat.Presheaf.germ R.obj ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
        (φ.hom.app (op U) r') :=
    (congrArg (unitStalkEquiv R y)
      (stalkMap_pullbackStalkComparison_tmul_germ f φ
        (_root_.SheafOfModules.unit (ringCatSheaf S))
        (_root_.SheafOfModules.pullbackObjUnitToUnit φ) y a U hy r')).trans
      ((map_smul (unitStalkEquiv R y) a _).trans
        (congrArg (a • ·)
          ((congrArg (fun t ↦ unitStalkEquiv R y
            (TopCat.Presheaf.germ (_root_.SheafOfModules.unit (ringCatSheaf R)).val.presheaf
              ((Opens.map f).obj U) y (Opens.mem_map.mpr hy) t)) h₁).trans
            (unitStalkEquiv_germ R y ((Opens.map f).obj U) (Opens.mem_map.mpr hy)
              (φ.hom.app (op U) r')))))
  have hR : TensorProduct.AlgebraTensorModule.rid ↑(TopCat.Presheaf.stalk S.obj (f y))
      ↑(TopCat.Presheaf.stalk R.obj y) ↑(TopCat.Presheaf.stalk R.obj y)
      (((unitStalkEquiv S (f y)).toLinearMap.baseChange ↑(TopCat.Presheaf.stalk R.obj y))
        (a ⊗ₜ TopCat.Presheaf.germ (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf
          U (f y) hy r)) =
      TopCat.Presheaf.germ S.obj U (f y) hy r' • a :=
    congrArg (fun t ↦ t • a) (unitStalkEquiv_germ S (f y) U hy r')
  have hmid : a • TopCat.Presheaf.germ R.obj ((Opens.map f).obj U) y (Opens.mem_map.mpr hy)
      (φ.hom.app (op U) r') = TopCat.Presheaf.germ S.obj U (f y) hy r' • a := by
    change a * _ = (stalkRingHom f φ y).hom (TopCat.Presheaf.germ S.obj U (f y) hy r') * a
    exact (congrArg (a * ·) (stalkRingHom_germ_apply f φ y U hy r').symm).trans (mul_comm a _)
  exact hL.trans (hmid.trans hR.symm)

/-- Pushforward of sheaves of modules along a composite continuous map `g ≫ f` is a right adjoint
whenever both factors are. -/
theorem isRightAdjoint_pushforward_comp {Z : TopCat.{u}} (g : Z ⟶ Y)
    {Q : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (ψ : ringCatSheaf R ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q))
    [(_root_.SheafOfModules.pushforward.{u} ψ).IsRightAdjoint] :
    (_root_.SheafOfModules.pushforward.{u} (compRingCatSheafHom f φ g ψ)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (_root_.SheafOfModules.pushforwardComp.{u} φ ψ)

/-- Compatibility of `pullbackStalkComparison` with composition of pullbacks along `g : Z ⟶ Y` and
`f : Y ⟶ X`, through `SheafOfModules.pullbackComp` and
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
theorem stalkMap_pullbackComp_inv_pullbackStalkComparison
    {Z : TopCat.{u}} (g : Z ⟶ Y)
    {Q : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
    (ψ : ringCatSheaf R ⟶
      ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf Q))
    [(_root_.SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]
    (G : _root_.SheafOfModules.{u} (ringCatSheaf S)) (z : Z) :
    letI : (_root_.SheafOfModules.pushforward.{u} (compRingCatSheafHom f φ g ψ)).IsRightAdjoint :=
      isRightAdjoint_pushforward_comp f φ g ψ
    let ρ : ↑(TopCat.Presheaf.stalk S.obj (f (g z))) →+* ↑(TopCat.Presheaf.stalk Q.obj z) :=
      (stalkRingHom (g ≫ f) (compRingCatSheafHom f φ g ψ) z).hom
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f (g z))) ↑(TopCat.Presheaf.stalk R.obj (g z)) :=
      (stalkRingHom f φ (g z)).hom.toAlgebra
    letI : Algebra ↑(TopCat.Presheaf.stalk R.obj (g z)) ↑(TopCat.Presheaf.stalk Q.obj z) :=
      (stalkRingHom g ψ z).hom.toAlgebra
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f (g z))) ↑(TopCat.Presheaf.stalk Q.obj z) :=
      ρ.toAlgebra
    haveI : IsScalarTower ↑(TopCat.Presheaf.stalk S.obj (f (g z)))
        ↑(TopCat.Presheaf.stalk R.obj (g z)) ↑(TopCat.Presheaf.stalk Q.obj z) :=
      IsScalarTower.of_algebraMap_eq'
        (congrArg CommRingCat.Hom.hom (stalkRingHom_comp f φ g ψ z))
    (_root_.SheafOfModules.stalkMap ((_root_.SheafOfModules.pullbackComp φ ψ).inv.app G) z).comp
        (pullbackStalkComparison (g ≫ f) (compRingCatSheafHom f φ g ψ) G z) =
      (pullbackStalkComparison g ψ ((_root_.SheafOfModules.pullback.{u} φ).obj G) z).comp
        (((pullbackStalkComparison f φ G (g z)).baseChange
            ↑(TopCat.Presheaf.stalk Q.obj z)).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            ↑(TopCat.Presheaf.stalk S.obj (f (g z)))
            ↑(TopCat.Presheaf.stalk R.obj (g z))
            ↑(TopCat.Presheaf.stalk Q.obj z)
            ↑(TopCat.Presheaf.stalk Q.obj z)
            ↑(TopCat.Presheaf.stalk G.val.presheaf (f (g z)))).symm.toLinearMap) := by
  let _ : (_root_.SheafOfModules.pushforward.{u} (compRingCatSheafHom f φ g ψ)).IsRightAdjoint :=
    isRightAdjoint_pushforward_comp f φ g ψ
  let ρ : ↑(TopCat.Presheaf.stalk S.obj (f (g z))) →+* ↑(TopCat.Presheaf.stalk Q.obj z) :=
    (stalkRingHom (g ≫ f) (compRingCatSheafHom f φ g ψ) z).hom
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f (g z))) ↑(TopCat.Presheaf.stalk R.obj (g z)) :=
    (stalkRingHom f φ (g z)).hom.toAlgebra
  let _ : Algebra ↑(TopCat.Presheaf.stalk R.obj (g z)) ↑(TopCat.Presheaf.stalk Q.obj z) :=
    (stalkRingHom g ψ z).hom.toAlgebra
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f (g z))) ↑(TopCat.Presheaf.stalk Q.obj z) :=
    ρ.toAlgebra
  have _ : IsScalarTower ↑(TopCat.Presheaf.stalk S.obj (f (g z)))
      ↑(TopCat.Presheaf.stalk R.obj (g z)) ↑(TopCat.Presheaf.stalk Q.obj z) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (stalkRingHom_comp f φ g ψ z))
  refine algebraTensor_ext (R₀ := ↑(TopCat.Presheaf.stalk S.obj (f (g z))))
    (N₀ := ↑(TopCat.Presheaf.stalk G.val.presheaf (f (g z)))) fun q s ↦ ?_
  obtain ⟨U, hz, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf s
  let m' : G.val.obj (op U) := m
  have hc := CategoryTheory.unit_conjugateEquiv
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).comp
      (_root_.SheafOfModules.pullbackPushforwardAdjunction ψ))
    (_root_.SheafOfModules.pullbackPushforwardAdjunction _)
    (_root_.SheafOfModules.pullbackComp φ ψ).inv G
  rw [_root_.SheafOfModules.conjugateEquiv_pullbackComp_inv] at hc
  have happ := (congrArg (fun k ↦ k.val.app (op U) m') hc).symm
  have hL := stalkMap_pullbackStalkComparison_tmul_germ (g ≫ f) (compRingCatSheafHom f φ g ψ) G
    ((_root_.SheafOfModules.pullbackComp φ ψ).inv.app G) z q U hz m'
  have hR :=
    (congrArg (fun t ↦ pullbackStalkComparison g ψ
      ((_root_.SheafOfModules.pullback.{u} φ).obj G) z (q ⊗ₜ t))
      (pullbackStalkComparison_one_tmul_germ f φ G (g z) U hz m')).trans
      (pullbackStalkComparison_tmul_germ g ψ ((_root_.SheafOfModules.pullback.{u} φ).obj G) z
        q ((Opens.map f).obj U) (Opens.mem_map.mpr hz) _)
  exact hL.trans
    ((congrArg (fun t ↦ q • TopCat.Presheaf.germ
      ((_root_.SheafOfModules.pullback.{u} ψ).obj
        ((_root_.SheafOfModules.pullback.{u} φ).obj G)).val.presheaf
      ((Opens.map g).obj ((Opens.map f).obj U)) z
      (Opens.mem_map.mpr (Opens.mem_map.mpr hz)) t) happ).trans hR.symm)

end PullbackStalk

end TauCeti.SheafOfModules

end
