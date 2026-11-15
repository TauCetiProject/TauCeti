/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Identity
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Stalk

/-!
# Strong symmetric monoidal structure on pullback of sheaves of modules

For a morphism `(f, φ)` of sheaves of commutative rings over arbitrary topological spaces and
arbitrary sheaves of modules `E` and `F` on the target, the canonical oplax monoidal comparison
`δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` and unit comparison `η : f^* 𝒪_X ⟶ 𝒪_Y` are isomorphisms, with
no quasi-coherence, flatness, or finiteness hypotheses.

The proof checks bijectivity on stalks at every point `y : Y`. Combining the pullback stalk
equivalence `(f^* G)_y ≃ₗ[R_y] R_y ⊗[S_{f(y)}] G_{f(y)}` (`pullbackStalkEquiv`) with the tensor
stalk equivalence `(M ⊗ N)_z ≃ₗ[R_z] M_z ⊗[R_z] N_z` (`tensorObjStalkEquiv`) identifies the stalk
map of `δ` with the canonical base-change distributivity equivalence
`R_y ⊗[S_{f(y)}] (E_{f(y)} ⊗[S_{f(y)}] F_{f(y)}) ≃ₗ[R_y]
  (R_y ⊗[S_{f(y)}] E_{f(y)}) ⊗[R_y] (R_y ⊗[S_{f(y)}] F_{f(y)})`
(`TensorProduct.AlgebraTensorModule.distribBaseChange`). Likewise, the stalk map of
`SheafOfModules.pullbackObjUnitToUnit φ` is identified through `unitStalkEquiv` with the right
unitor `R_y ⊗[S_{f(y)}] S_{f(y)} ≃ₗ[R_y] R_y`.

## Main declarations

* `TauCeti.SheafOfModules.pullback_δ_val_app_unit_μ_tmul`: action of the oplax tensorator `δ` on
  pulled-back pure tensors of sections;
* `TauCeti.SheafOfModules.tensorObjStalkComparison_stalkMap_pullback_δ_pullbackStalkComparison`:
  commutativity of the stalk map of `δ` with `pullbackStalkComparison`, `tensorObjStalkComparison`,
  and `TensorProduct.AlgebraTensorModule.distribBaseChange`;
* `TauCeti.SheafOfModules.isIso_pullbackObjUnitToUnit` and
  `TauCeti.SheafOfModules.isIso_pullback_δ`: invertibility of the unit and tensor comparisons of
  module pullback;
* `TauCeti.SheafOfModules.pullbackTensorIso` and `TauCeti.SheafOfModules.pullbackUnitIso`: the
  resulting isomorphisms `f^* (E ⊗ F) ≅ f^* E ⊗ f^* F` and `f^* 𝒪_X ≅ 𝒪_Y`;
* `TauCeti.SheafOfModules.pullbackMonoidal` and `TauCeti.SheafOfModules.pullbackBraided`: the
  strong symmetric monoidal structure on `SheafOfModules.pullback φ`;
* `TauCeti.SheafOfModules.isMonoidal_pullbackId_hom` and
  `TauCeti.SheafOfModules.isMonoidal_pullbackComp_hom`: monoidal coherence of `pullbackId` and
  `pullbackComp`.

## References

* [The Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD).
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace TauCeti.SheafOfModules

universe u

noncomputable section

private theorem algebraTensor_ext {R₀ A₀ N₀ P₀ : Type*} [CommRing R₀] [CommRing A₀]
    [Algebra R₀ A₀] [AddCommGroup N₀] [Module R₀ N₀] [AddCommGroup P₀] [Module A₀ P₀]
    {g h : A₀ ⊗[R₀] N₀ →ₗ[A₀] P₀} (H : ∀ a n, g (a ⊗ₜ n) = h (a ⊗ₜ n)) : g = h := by
  let _ : Module R₀ P₀ := Module.compHom P₀ (algebraMap R₀ A₀)
  have _ : IsScalarTower R₀ A₀ P₀ := IsScalarTower.of_compHom R₀ A₀ P₀
  exact LinearMap.restrictScalars_injective R₀
    (TensorProduct.ext' (fun a n ↦ H a n))

variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj (ringCatSheaf R))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- The oplax tensor comparison `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` carries the pulled-back image
of a pure tensor `m ⊗ₜ n` over `U` to the image of the pure tensor of the pulled-back sections
over `f⁻¹(U)`. -/
theorem pullback_δ_val_app_unit_μ_tmul
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) (U : Opens X)
    (m : E.val.obj (op U)) (n : F.val.obj (op U)) :
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F).val.app
        (op ((Opens.map f).obj U))
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app (E ⊗ F)).val.app
          (op U)
          (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf S)) E F).app
            (op U)) (m ⊗ₜ[S.obj.obj (op U)] n))) =
      ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R))
          ((_root_.SheafOfModules.pullback.{u} φ).obj E)
          ((_root_.SheafOfModules.pullback.{u} φ).obj F)).app (op ((Opens.map f).obj U)))
        ((((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app E).val.app (op U) m)
          ⊗ₜ[R.obj.obj (op ((Opens.map f).obj U))]
          (((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app F).val.app
            (op U) n)) := by
  let adj := _root_.SheafOfModules.pullbackPushforwardAdjunction φ
  have h := congrArg (fun k ↦ k.val.app (op U)
      (((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf S)) E F).app
        (op U)) (m ⊗ₜ[S.obj.obj (op U)] n)))
    (adj.unit_app_tensor_comp_map_δ E F)
  have hn := congrArg (fun k ↦ k.app (op U) (m ⊗ₜ[S.obj.obj (op U)] n))
    (Functor.LaxMonoidal.μ_natural (_root_.SheafOfModules.forget (ringCatSheaf S))
      (adj.unit.app E) (adj.unit.app F))
  have hp := pushforward_μ_app_tmul φ ((_root_.SheafOfModules.pullback.{u} φ).obj E)
    ((_root_.SheafOfModules.pullback.{u} φ).obj F) (op U)
    ((adj.unit.app E).val.app (op U) m) ((adj.unit.app F).val.app (op U) n)
  exact h.trans ((congrArg
    ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ)
      ((_root_.SheafOfModules.pullback.{u} φ).obj E)
      ((_root_.SheafOfModules.pullback.{u} φ).obj F)).val.app (op U)) hn.symm).trans hp)

private theorem stalk_pullback_δ_tmul_germ
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y)
    (a : ↑(TopCat.Presheaf.stalk R.obj y)) (V : Opens X) (hyV : f y ∈ V)
    (m₁ : E.val.obj (op V)) (n₀ : F.val.obj (op V)) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    tensorObjStalkComparison R ((_root_.SheafOfModules.pullback.{u} φ).obj E)
        ((_root_.SheafOfModules.pullback.{u} φ).obj F) y
        (_root_.SheafOfModules.stalkMap
          (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) y
          (pullbackStalkComparison f φ (E ⊗ F) y
            (a ⊗ₜ (tensorObjStalkEquiv S E F (f y)).symm
              (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m₁ ⊗ₜ
                TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n₀)))) =
      TensorProduct.map (pullbackStalkComparison f φ E y) (pullbackStalkComparison f φ F y)
        (TensorProduct.AlgebraTensorModule.distribBaseChange
          ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) _ _
          (a ⊗ₜ tensorObjStalkComparison S E F (f y)
            ((tensorObjStalkEquiv S E F (f y)).symm
              (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m₁ ⊗ₜ
                TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n₀)))) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  let P := _root_.SheafOfModules.pullback.{u} φ
  let tR := tensorObjStalkComparison R (P.obj E) (P.obj F) y
  let gE := TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m₁
  let gF := TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n₀
  let pMap := TensorProduct.map (pullbackStalkComparison f φ E y) (pullbackStalkComparison f φ F y)
  have h₁ := congrArg (fun z ↦ tR (_root_.SheafOfModules.stalkMap
      (Functor.OplaxMonoidal.δ P E F) y (pullbackStalkComparison f φ (E ⊗ F) y (a ⊗ₜ z))))
    (tensorObjStalkEquiv_symm_tmul_germ S E F (f y) V hyV m₁ n₀)
  have h₂ := (congrArg tR (stalkMap_pullbackStalkComparison_tmul_germ f φ (E ⊗ F)
      (Functor.OplaxMonoidal.δ P E F) y a V hyV _)).trans
    ((map_smul tR a _).trans (congrArg (a • ·)
      ((congrArg (fun s ↦ tR (TopCat.Presheaf.germ (P.obj E ⊗ P.obj F).val.presheaf
        ((Opens.map f).obj V) y (Opens.mem_map.mpr hyV) s))
        (pullback_δ_val_app_unit_μ_tmul f φ E F V m₁ n₀)).trans
        (tensorObjStalkComparison_germ_μ_tmul R (P.obj E) (P.obj F) y ((Opens.map f).obj V)
          (Opens.mem_map.mpr hyV) _ _))))
  have he : tensorObjStalkComparison S E F (f y)
      ((tensorObjStalkEquiv S E F (f y)).symm (gE ⊗ₜ gF)) = gE ⊗ₜ gF :=
    (tensorObjStalkEquiv_apply S E F (f y) _).symm.trans
      ((tensorObjStalkEquiv S E F (f y)).apply_symm_apply _)
  have hR := (congrArg (fun z ↦ pMap (TensorProduct.AlgebraTensorModule.distribBaseChange
        ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) _ _ (a ⊗ₜ z)))
      he).trans
    ((congrArg pMap (TensorProduct.AlgebraTensorModule.distribBaseChange_tmul
      ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) gE gF a)).trans
      ((TensorProduct.map_tmul (pullbackStalkComparison f φ E y)
          (pullbackStalkComparison f φ F y) _ _).trans
        ((congrArg₂ (· ⊗ₜ ·) (pullbackStalkComparison_tmul_germ f φ E y a V hyV m₁)
          (pullbackStalkComparison_one_tmul_germ f φ F y V hyV n₀)).trans
          (TensorProduct.smul_tmul' a _ _))))
  exact (h₁.trans h₂).trans hR.symm

/-- At every point `y : Y`, the stalk map of the oplax tensor comparison
`δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` intertwines `pullbackStalkComparison` and
`tensorObjStalkComparison` via `TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
theorem tensorObjStalkComparison_stalkMap_pullback_δ_pullbackStalkComparison
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
      (stalkRingHom f φ y).hom.toAlgebra
    (tensorObjStalkComparison R
        ((_root_.SheafOfModules.pullback.{u} φ).obj E)
        ((_root_.SheafOfModules.pullback.{u} φ).obj F) y).comp
      ((_root_.SheafOfModules.stalkMap
          (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) y).comp
        (pullbackStalkComparison f φ (E ⊗ F) y)) =
      (TensorProduct.map
          (pullbackStalkComparison f φ E y)
          (pullbackStalkComparison f φ F y)).comp
        ((TensorProduct.AlgebraTensorModule.distribBaseChange
            ↑(TopCat.Presheaf.stalk S.obj (f y))
            ↑(TopCat.Presheaf.stalk R.obj y)
            ↑(TopCat.Presheaf.stalk E.val.presheaf (f y))
            ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))).toLinearMap.comp
          ((tensorObjStalkComparison S E F (f y)).baseChange
            ↑(TopCat.Presheaf.stalk R.obj y))) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  let e := (tensorObjStalkEquiv S E F (f y)).symm
  let L := (tensorObjStalkComparison R ((_root_.SheafOfModules.pullback.{u} φ).obj E)
      ((_root_.SheafOfModules.pullback.{u} φ).obj F) y).comp
    ((_root_.SheafOfModules.stalkMap
        (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) y).comp
      (pullbackStalkComparison f φ (E ⊗ F) y))
  let M := (TensorProduct.map (pullbackStalkComparison f φ E y)
      (pullbackStalkComparison f φ F y)).comp
    ((TensorProduct.AlgebraTensorModule.distribBaseChange
        ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y)
        ↑(TopCat.Presheaf.stalk E.val.presheaf (f y))
        ↑(TopCat.Presheaf.stalk F.val.presheaf (f y))).toLinearMap.comp
      ((tensorObjStalkComparison S E F (f y)).baseChange ↑(TopCat.Presheaf.stalk R.obj y)))
  change L = M
  apply algebraTensor_ext
  intro a s
  obtain ⟨t, rfl⟩ := e.surjective s
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    obtain ⟨U, hyU, m₀, hu⟩ := TopCat.Presheaf.exists_germ_eq E.val.presheaf u
    obtain ⟨V, hVU, hyV, n₀, hv⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf v hyU
    let m₁ : E.val.obj (op V) := E.val.map (homOfLE hVU).op m₀
    have hu' : u = TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m₁ :=
      hu.symm.trans (TopCat.Presheaf.germ_res_apply E.val.presheaf (homOfLE hVU) (f y) hyV m₀).symm
    have hM := congrArg (fun z ↦ TensorProduct.map
        (pullbackStalkComparison f φ E y) (pullbackStalkComparison f φ F y)
        (TensorProduct.AlgebraTensorModule.distribBaseChange
          ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) _ _ z))
      ((tensorObjStalkComparison S E F (f y)).baseChange_tmul a
        (e (TopCat.Presheaf.germ E.val.presheaf V (f y) hyV m₁ ⊗ₜ
          TopCat.Presheaf.germ F.val.presheaf V (f y) hyV n₀)))
    exact (congrArg (fun z ↦ L (a ⊗ₜ e z)) (congrArg₂ (· ⊗ₜ ·) hu' hv.symm)).trans
      ((stalk_pullback_δ_tmul_germ f φ E F y a V hyV m₁ n₀).trans
        (hM.symm.trans
          (congrArg (fun z ↦ M (a ⊗ₜ e z)) (congrArg₂ (· ⊗ₜ ·) hu' hv.symm)).symm))
  | add z w hz hw =>
    have hLz := (congrArg (fun q ↦ L (a ⊗ₜ q)) (e.map_add z w)).trans
      ((congrArg L (TensorProduct.tmul_add a _ _)).trans (L.map_add _ _))
    have hMz := (congrArg (fun q ↦ M (a ⊗ₜ q)) (e.map_add z w)).trans
      ((congrArg M (TensorProduct.tmul_add a _ _)).trans (M.map_add _ _))
    exact hLz.trans ((congrArg₂ (· + ·) hz hw).trans hMz.symm)

/-- At every point `y : Y`, the stalk map of `SheafOfModules.pullbackObjUnitToUnit φ` is
bijective. -/
theorem bijective_stalkMap_pullbackObjUnitToUnit (y : Y) :
    Function.Bijective
      (_root_.SheafOfModules.stalkMap (_root_.SheafOfModules.pullbackObjUnitToUnit φ) y) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  let eR : ↑(TopCat.Presheaf.stalk R.obj y) ⊗[↑(TopCat.Presheaf.stalk S.obj (f y))]
      ↑(TopCat.Presheaf.stalk
        (_root_.SheafOfModules.unit (ringCatSheaf S)).val.presheaf (f y)) ≃ₗ[
        ↑(TopCat.Presheaf.stalk R.obj y)]
      ↑(TopCat.Presheaf.stalk R.obj y) :=
    ((unitStalkEquiv S (f y)).baseChange
      ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) _ _).trans
      (TensorProduct.AlgebraTensorModule.rid
        ↑(TopCat.Presheaf.stalk S.obj (f y))
        ↑(TopCat.Presheaf.stalk R.obj y)
        ↑(TopCat.Presheaf.stalk R.obj y))
  have hEq : ((unitStalkEquiv R y : _ → _) ∘
      (_root_.SheafOfModules.stalkMap (_root_.SheafOfModules.pullbackObjUnitToUnit φ) y : _ → _) ∘
        (pullbackStalkComparison f φ (_root_.SheafOfModules.unit (ringCatSheaf S)) y : _ → _)) =
      (eR : _ → _) :=
    congrArg DFunLike.coe
      (unitStalkEquiv_stalkMap_pullbackObjUnitToUnit_pullbackStalkComparison f φ y)
  have hbij : Function.Bijective ((unitStalkEquiv R y : _ → _) ∘
      (_root_.SheafOfModules.stalkMap (_root_.SheafOfModules.pullbackObjUnitToUnit φ) y : _ → _) ∘
        (pullbackStalkComparison f φ (_root_.SheafOfModules.unit (ringCatSheaf S)) y : _ → _)) :=
    hEq.symm ▸ eR.bijective
  exact (Function.Bijective.of_comp_iff _
    (pullbackStalkComparison_bijective f φ
      (_root_.SheafOfModules.unit (ringCatSheaf S)) y)).mp
      ((Function.Bijective.of_comp_iff' (unitStalkEquiv R y).bijective _).mp hbij)

/-- At every point `y : Y`, the stalk map of the oplax tensor comparison
`δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` is bijective. -/
@[stacks 01CD]
theorem bijective_stalkMap_pullback_δ
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    Function.Bijective
      (_root_.SheafOfModules.stalkMap
        (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) y) := by
  let _ : Algebra ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) :=
    (stalkRingHom f φ y).hom.toAlgebra
  let eR := (((tensorObjStalkEquiv S E F (f y)).baseChange
      ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) _ _).trans
    (TensorProduct.AlgebraTensorModule.distribBaseChange
      ↑(TopCat.Presheaf.stalk S.obj (f y)) ↑(TopCat.Presheaf.stalk R.obj y) _ _)).trans
    (TensorProduct.congr (pullbackStalkEquiv f φ E y) (pullbackStalkEquiv f φ F y))
  have heS : tensorObjStalkComparison S E F (f y) =
      (tensorObjStalkEquiv S E F (f y)).toLinearMap :=
    LinearMap.ext fun z ↦ (tensorObjStalkEquiv_apply S E F (f y) z).symm
  have heE : pullbackStalkComparison f φ E y = (pullbackStalkEquiv f φ E y).toLinearMap :=
    LinearMap.ext fun z ↦ (pullbackStalkEquiv_apply f φ E y z).symm
  have heF : pullbackStalkComparison f φ F y = (pullbackStalkEquiv f φ F y).toLinearMap :=
    LinearMap.ext fun z ↦ (pullbackStalkEquiv_apply f φ F y z).symm
  have hLin := tensorObjStalkComparison_stalkMap_pullback_δ_pullbackStalkComparison f φ E F y
  rw [heS, heE, heF] at hLin
  have hEq : ((tensorObjStalkComparison R ((_root_.SheafOfModules.pullback.{u} φ).obj E)
          ((_root_.SheafOfModules.pullback.{u} φ).obj F) y : _ → _) ∘
        (_root_.SheafOfModules.stalkMap
          (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) y : _ → _) ∘
        (pullbackStalkComparison f φ (E ⊗ F) y : _ → _)) = (eR : _ → _) :=
    congrArg DFunLike.coe hLin
  have hbij : Function.Bijective
      ((tensorObjStalkComparison R ((_root_.SheafOfModules.pullback.{u} φ).obj E)
          ((_root_.SheafOfModules.pullback.{u} φ).obj F) y : _ → _) ∘
        (_root_.SheafOfModules.stalkMap
          (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) y : _ → _) ∘
        (pullbackStalkComparison f φ (E ⊗ F) y : _ → _)) :=
    hEq.symm ▸ eR.bijective
  exact (Function.Bijective.of_comp_iff _
    (pullbackStalkComparison_bijective f φ (E ⊗ F) y)).mp
      ((Function.Bijective.of_comp_iff'
        (tensorObjStalkComparison_bijective R
          ((_root_.SheafOfModules.pullback.{u} φ).obj E)
          ((_root_.SheafOfModules.pullback.{u} φ).obj F) y) _).mp hbij)

/-- The canonical unit comparison `f^* 𝒪_X ⟶ 𝒪_Y` of module pullback over topological spaces is an
isomorphism. -/
instance isIso_pullbackObjUnitToUnit :
    IsIso (_root_.SheafOfModules.pullbackObjUnitToUnit φ) :=
  (_root_.SheafOfModules.isIso_iff_stalkMap_bijective _).mpr
    (bijective_stalkMap_pullbackObjUnitToUnit f φ)

/-- The oplax unit comparison `η : f^* 𝒪_X ⟶ 𝒪_Y` of module pullback over topological spaces is an
isomorphism. -/
instance isIso_pullback_η :
    IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ)) :=
  (pullback_η φ).symm ▸ inferInstance

/-- The oplax tensor comparison `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` of module pullback over
topological spaces is an isomorphism for arbitrary sheaves of modules `E` and `F`. -/
@[stacks 01CD]
instance isIso_pullback_δ (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) :=
  (_root_.SheafOfModules.isIso_iff_stalkMap_bijective _).mpr
    (bijective_stalkMap_pullback_δ f φ E F)

/-- The canonical isomorphism `f^* 𝒪_X ≅ 𝒪_Y` for pullback of sheaves of modules over topological
spaces. -/
def pullbackUnitIso :
    (_root_.SheafOfModules.pullback.{u} φ).obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso (_root_.SheafOfModules.pullbackObjUnitToUnit φ)

@[simp]
theorem pullbackUnitIso_hom :
    (pullbackUnitIso f φ).hom = _root_.SheafOfModules.pullbackObjUnitToUnit φ :=
  (rfl)

/-- The canonical isomorphism `f^* (E ⊗ F) ≅ f^* E ⊗ f^* F` for arbitrary sheaves of modules over
topological spaces. -/
@[stacks 01CD]
def pullbackTensorIso (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (_root_.SheafOfModules.pullback.{u} φ).obj (E ⊗ F) ≅
      (_root_.SheafOfModules.pullback.{u} φ).obj E ⊗
        (_root_.SheafOfModules.pullback.{u} φ).obj F :=
  asIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F)

@[simp]
theorem pullbackTensorIso_hom (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackTensorIso f φ E F).hom =
      Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F :=
  (rfl)

theorem pullbackTensorIso_inv (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackTensorIso f φ E F).inv =
      inv (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) :=
  (rfl)

/-- Pullback of sheaves of modules along a morphism of ringed spaces is strong monoidal, with no
quasi-coherence or finiteness hypotheses. -/
@[stacks 01CD]
instance pullbackMonoidal : (_root_.SheafOfModules.pullback.{u} φ).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (_root_.SheafOfModules.pullback.{u} φ)

theorem pullback_μ (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} φ) E F =
      inv (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F) :=
  IsIso.eq_inv_of_hom_inv_id (Functor.Monoidal.δ_μ _ E F)

@[simp]
theorem pullback_ε :
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ) =
      inv (_root_.SheafOfModules.pullbackObjUnitToUnit φ) :=
  IsIso.eq_inv_of_inv_hom_id
    ((congrArg (_ ≫ ·) (pullback_η φ).symm).trans (Functor.Monoidal.ε_η _))

/-- Pullback of sheaves of modules along a morphism of ringed spaces is strong symmetric
monoidal. -/
instance pullbackBraided : (_root_.SheafOfModules.pullback.{u} φ).Braided where
  toMonoidal := pullbackMonoidal f φ
  braided E F := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F),
      ← cancel_mono (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) F E),
      Functor.Monoidal.δ_μ_assoc, Category.assoc, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
    exact pullback_map_braiding_hom_comp_δ φ E F

section IdentityAndComp

/-- Strong monoidal structure on identity pullback `SheafOfModules.pullback (𝟙 (ringCatSheaf S))`
written over `𝟭 (Opens X)`. -/
@[instance_reducible]
def pullbackIdMonoidal (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    (_root_.SheafOfModules.pullback.{u}
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology X)
      (S := ringCatSheaf S) (R := ringCatSheaf S) (F := 𝟭 (Opens X))
      (𝟙 (ringCatSheaf S))).Monoidal :=
  letI := pullbackOplaxMonoidal (S := S) (R := S) (F := 𝟭 (Opens X)) (𝟙 (ringCatSheaf S))
  haveI : IsIso (Functor.OplaxMonoidal.η
      (_root_.SheafOfModules.pullback.{u}
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology X)
        (S := ringCatSheaf S) (R := ringCatSheaf S) (F := 𝟭 (Opens X))
        (𝟙 (ringCatSheaf S)))) := by
    rw [pullback_id_η S]
    infer_instance
  haveI (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
      IsIso (Functor.OplaxMonoidal.δ
        (_root_.SheafOfModules.pullback.{u}
          (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology X)
          (S := ringCatSheaf S) (R := ringCatSheaf S) (F := 𝟭 (Opens X))
          (𝟙 (ringCatSheaf S))) E F) := by
    let δId := Functor.OplaxMonoidal.δ
      (_root_.SheafOfModules.pullback.{u}
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology X)
        (S := ringCatSheaf S) (R := ringCatSheaf S) (F := 𝟭 (Opens X))
        (𝟙 (ringCatSheaf S))) E F
    let gId := (_root_.SheafOfModules.pullbackId (ringCatSheaf S)).hom.app E ⊗ₘ
      (_root_.SheafOfModules.pullbackId (ringCatSheaf S)).hom.app F
    have : IsIso (δId ≫ gId) := (pullback_id_δ S E F).symm ▸ inferInstance
    exact IsIso.of_isIso_comp_right δId gId
  Functor.Monoidal.ofOplaxMonoidal _

/-- The canonical identity isomorphism `SheafOfModules.pullbackId` is monoidal. -/
theorem isMonoidal_pullbackId_hom (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    letI := pullbackIdMonoidal S
    NatTrans.IsMonoidal (_root_.SheafOfModules.pullbackId.{u} (ringCatSheaf S)).hom := by
  let _ := pullbackIdMonoidal S
  refine { unit := ?_, tensor := fun E F ↦ ?_ }
  · rw [Functor.LaxMonoidal.id_ε, ← pullback_id_η S]
    exact Functor.Monoidal.ε_η _
  · rw [← cancel_epi (Functor.OplaxMonoidal.δ
        (_root_.SheafOfModules.pullback.{u}
          (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology X)
          (S := ringCatSheaf S) (R := ringCatSheaf S) (F := 𝟭 (Opens X))
          (𝟙 (ringCatSheaf S))) E F),
      Functor.Monoidal.δ_μ_assoc, Functor.LaxMonoidal.id_μ, Category.comp_id]
    exact (pullback_id_δ S E F).symm

variable {Z : TopCat.{u}} (g : Z ⟶ Y)
  {T : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
  (ψ : ringCatSheaf R ⟶
    ((Opens.map g).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z)).obj (ringCatSheaf T))
  [(_root_.SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]

/-- Strong monoidal structure on pullback along the composite `(φ, ψ)` written over
`Opens.map f ⋙ Opens.map g`. -/
@[instance_reducible]
def pullbackCompTargetMonoidal :
    haveI := isRightAdjoint_pushforward_comp f φ g ψ
    (_root_.SheafOfModules.pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)).Monoidal :=
  haveI := isRightAdjoint_pushforward_comp f φ g ψ
  letI := pullbackOplaxMonoidal (F := Opens.map f ⋙ Opens.map g) (S := S) (R := T)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)
  haveI : IsIso (Functor.OplaxMonoidal.η
      (_root_.SheafOfModules.pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
        (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))) := by
    rw [pullback_comp_η φ ψ]
    infer_instance
  haveI (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
      IsIso (Functor.OplaxMonoidal.δ
        (_root_.SheafOfModules.pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
          (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
            (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) E F) := by
    rw [pullback_comp_δ φ ψ E F]
    infer_instance
  Functor.Monoidal.ofOplaxMonoidal _

private theorem pullbackComp_hom_tensor
    (E F : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    haveI := isRightAdjoint_pushforward_comp f φ g ψ
    letI := pullbackCompTargetMonoidal f φ g ψ
    Functor.LaxMonoidal.μ
        (_root_.SheafOfModules.pullback.{u} φ ⋙ _root_.SheafOfModules.pullback.{u} ψ) E F ≫
      (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (E ⊗ F) =
      ((_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app E ⊗ₘ
        (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app F) ≫
        Functor.LaxMonoidal.μ _ E F := by
  have := isRightAdjoint_pushforward_comp f φ g ψ
  let _ := pullbackCompTargetMonoidal f φ g ψ
  let δC := Functor.OplaxMonoidal.δ
    (_root_.SheafOfModules.pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) E F
  have : IsIso δC := by
    change IsIso (Functor.OplaxMonoidal.δ _ E F); rw [pullback_comp_δ φ ψ E F]; infer_instance
  apply (cancel_mono δC).mp
  let p₁ := Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} ψ)
    ((_root_.SheafOfModules.pullback.{u} φ).obj E) ((_root_.SheafOfModules.pullback.{u} φ).obj F)
  let p₂ := (_root_.SheafOfModules.pullback.{u} ψ).map
    (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pullback.{u} φ) E F)
  let q₂ := (_root_.SheafOfModules.pullback.{u} ψ).map
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} φ) E F)
  let q₁ := Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback.{u} ψ)
    ((_root_.SheafOfModules.pullback.{u} φ).obj E) ((_root_.SheafOfModules.pullback.{u} φ).obj F)
  let w := (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app E ⊗ₘ
    (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app F
  have hR : (w ≫ Functor.LaxMonoidal.μ _ E F) ≫ δC = w :=
    (Category.assoc _ _ δC).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_δ _ E F)).trans (Category.comp_id _))
  have hδ : (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (E ⊗ F) ≫ δC = q₂ ≫ q₁ ≫ w :=
    (congrArg (_ ≫ ·) (pullback_comp_δ φ ψ E F)).trans
      (Iso.hom_inv_id_app_assoc (_root_.SheafOfModules.pullbackComp.{u} φ ψ) (E ⊗ F) _)
  have hp₂q₂ : p₂ ≫ q₂ = 𝟙 _ :=
    ((_root_.SheafOfModules.pullback.{u} ψ).map_comp _ _).symm.trans
      ((congrArg (_root_.SheafOfModules.pullback.{u} ψ).map
        (Functor.Monoidal.μ_δ (_root_.SheafOfModules.pullback.{u} φ) E F)).trans
        ((_root_.SheafOfModules.pullback.{u} ψ).map_id _))
  have hp₁q₁ : p₁ ≫ q₁ = 𝟙 _ := Functor.Monoidal.μ_δ (_root_.SheafOfModules.pullback.{u} ψ) _ _
  have hL₁ : (Functor.LaxMonoidal.μ
        (_root_.SheafOfModules.pullback.{u} φ ⋙ _root_.SheafOfModules.pullback.{u} ψ) E F ≫
      (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (E ⊗ F)) ≫ δC =
      p₁ ≫ p₂ ≫ q₂ ≫ q₁ ≫ w :=
    (congrArg (fun m ↦ (m ≫ (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom.app (E ⊗ F)) ≫ δC)
      (Functor.LaxMonoidal.comp_μ _ _ E F)).trans
      ((Category.assoc (p₁ ≫ p₂) _ δC).trans
        ((Category.assoc p₁ p₂ _).trans (congrArg (p₁ ≫ p₂ ≫ ·) hδ)))
  have hL₂ : p₁ ≫ p₂ ≫ q₂ ≫ q₁ ≫ w = w :=
    (congrArg (p₁ ≫ ·)
      ((Category.assoc p₂ q₂ (q₁ ≫ w)).symm.trans
        ((congrArg (· ≫ (q₁ ≫ w)) hp₂q₂).trans (Category.id_comp _)))).trans
      ((Category.assoc p₁ q₁ w).symm.trans
        ((congrArg (· ≫ w) hp₁q₁).trans (Category.id_comp w)))
  exact (hL₁.trans hL₂).trans hR.symm

/-- The canonical composition isomorphism `SheafOfModules.pullbackComp` is monoidal. -/
theorem isMonoidal_pullbackComp_hom :
    haveI := isRightAdjoint_pushforward_comp f φ g ψ
    letI := pullbackCompTargetMonoidal f φ g ψ
    NatTrans.IsMonoidal (_root_.SheafOfModules.pullbackComp.{u} φ ψ).hom := by
  have := isRightAdjoint_pushforward_comp f φ g ψ
  let _ := pullbackCompTargetMonoidal f φ g ψ
  have : IsIso (Functor.OplaxMonoidal.η
      (_root_.SheafOfModules.pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
        (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))) := by
    rw [pullback_comp_η φ ψ]
    infer_instance
  refine { unit := ?_, tensor := fun E F ↦ pullbackComp_hom_tensor f φ g ψ E F }
  rw [← cancel_mono (Functor.OplaxMonoidal.η
      (_root_.SheafOfModules.pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
        (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))),
    Category.assoc, Functor.Monoidal.ε_η, pullback_comp_η φ ψ, Iso.hom_inv_id_app_assoc,
    Functor.LaxMonoidal.comp_ε, Category.assoc, ← Functor.map_comp_assoc, Functor.Monoidal.ε_η,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.Monoidal.ε_η]

end IdentityAndComp

end

end TauCeti.SheafOfModules
