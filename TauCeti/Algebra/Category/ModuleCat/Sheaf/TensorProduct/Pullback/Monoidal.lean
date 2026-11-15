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

Identifies the stalk maps of `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` and `pullbackObjUnitToUnit φ` via
`distribBaseChange` and `rid`, deduces both are isomorphisms, and equips `SheafOfModules.pullback φ`
with `Functor.Monoidal` and `Functor.Braided` instances compatibly with `pullbackId`/`pullbackComp`
(Tag 01CD).
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace TopCat.Presheaf
open TauCeti.SheafOfModules (ringCatSheaf tensorObjStalkComparison
  tensorObjStalkComparison_bijective tensorObjStalkComparison_germ_μ_tmul tensorObjStalkEquiv
  tensorObjStalkEquiv_apply tensorObjStalkEquiv_symm_tmul_germ pullback_id_η pullback_id_δ)
open scoped TensorProduct
universe u
noncomputable section
namespace SheafOfModules
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
  {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj (ringCatSheaf R))
  [(pushforward.{u} φ).IsRightAdjoint]

/-- The oplax tensor comparison `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` carries the pulled-back image
of a pure tensor `m ⊗ₜ n` over `U` to the image of the pure tensor of the pulled-back sections. -/
theorem pullback_δ_val_app_unit_μ_tmul
    (E F : SheafOfModules.{u} (ringCatSheaf S)) (U : Opens X)
    (m : E.val.obj (op U)) (n : F.val.obj (op U)) :
    (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F).val.app (op ((Opens.map f).obj U))
        (((pullbackPushforwardAdjunction φ).unit.app (E ⊗ F)).val.app (op U)
          (((Functor.LaxMonoidal.μ (forget (ringCatSheaf S)) E F).app (op U))
            (m ⊗ₜ[S.obj.obj (op U)] n))) =
      ((Functor.LaxMonoidal.μ (forget (ringCatSheaf R))
          ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F)).app (op ((Opens.map f).obj U)))
        ((((pullbackPushforwardAdjunction φ).unit.app E).val.app (op U) m)
          ⊗ₜ[R.obj.obj (op ((Opens.map f).obj U))]
          (((pullbackPushforwardAdjunction φ).unit.app F).val.app (op U) n)) := by
  let adj := pullbackPushforwardAdjunction φ
  have h := congrArg (fun k ↦ k.val.app (op U)
      (((Functor.LaxMonoidal.μ (forget (ringCatSheaf S)) E F).app (op U))
        (m ⊗ₜ[S.obj.obj (op U)] n))) (adj.unit_app_tensor_comp_map_δ E F)
  have hn := congrArg (fun k ↦ k.app (op U) (m ⊗ₜ[S.obj.obj (op U)] n))
    (Functor.LaxMonoidal.μ_natural (forget (ringCatSheaf S)) (adj.unit.app E) (adj.unit.app F))
  have hp := pushforward_μ_app_tmul φ ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) (op U)
    ((adj.unit.app E).val.app (op U) m) ((adj.unit.app F).val.app (op U) n)
  exact h.trans ((congrArg ((Functor.LaxMonoidal.μ (pushforward φ)
    ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F)).val.app (op U)) hn.symm).trans hp)

/-- At every point `y : Y`, the stalk map of `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` intertwines
`pullbackStalkComparison` and `tensorObjStalkComparison` via `distribBaseChange`. -/
theorem tensorObjStalkComparison_stalkMap_pullback_δ_pullbackStalkComparison
    (E F : SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    letI : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
    (tensorObjStalkComparison R ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y).comp
      ((stalkMap (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) y).comp
        (pullbackStalkComparison f φ (E ⊗ F) y)) =
      (TensorProduct.map (pullbackStalkComparison f φ E y)
          (pullbackStalkComparison f φ F y)).comp
        ((TensorProduct.AlgebraTensorModule.distribBaseChange
            ↑(stalk S.obj (f y)) ↑(stalk R.obj y)
            ↑(stalk E.val.presheaf (f y)) ↑(stalk F.val.presheaf (f y))).toLinearMap.comp
          ((tensorObjStalkComparison S E F (f y)).baseChange ↑(stalk R.obj y))) := by
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  let P := pullback.{u} φ
  let e := (tensorObjStalkEquiv S E F (f y)).symm
  let pMap := TensorProduct.map (pullbackStalkComparison f φ E y) (pullbackStalkComparison f φ F y)
  let tR := tensorObjStalkComparison R (P.obj E) (P.obj F) y
  let L := tR.comp ((stalkMap (Functor.OplaxMonoidal.δ P E F) y).comp
    (pullbackStalkComparison f φ (E ⊗ F) y))
  let M := pMap.comp ((TensorProduct.AlgebraTensorModule.distribBaseChange
      ↑(stalk S.obj (f y)) ↑(stalk R.obj y)
      ↑(stalk E.val.presheaf (f y)) ↑(stalk F.val.presheaf (f y))).toLinearMap.comp
    ((tensorObjStalkComparison S E F (f y)).baseChange ↑(stalk R.obj y)))
  let Cod := ↑(stalk (P.obj E).val.presheaf y) ⊗[↑(stalk R.obj y)] ↑(stalk (P.obj F).val.presheaf y)
  let _ : Module ↑(stalk S.obj (f y)) Cod :=
    Module.compHom Cod (algebraMap ↑(stalk S.obj (f y)) ↑(stalk R.obj y))
  have _ : IsScalarTower ↑(stalk S.obj (f y)) ↑(stalk R.obj y) Cod := IsScalarTower.of_compHom _ _ _
  change L = M
  refine TensorProduct.AlgebraTensorModule.ext fun a s ↦ ?_
  obtain ⟨t, rfl⟩ := e.surjective s
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    obtain ⟨U, hyU, m₀, hu⟩ := exists_germ_eq E.val.presheaf u
    obtain ⟨V, hVU, hyV, n₀, hv⟩ := exists_le_germ_eq F.val.presheaf v hyU
    let m₁ : E.val.obj (op V) := E.val.map (homOfLE hVU).op m₀
    let gE := germ E.val.presheaf V (f y) hyV m₁
    let gF := germ F.val.presheaf V (f y) hyV n₀
    have hu' : u = gE :=
      hu.symm.trans (germ_res_apply E.val.presheaf (homOfLE hVU) (f y) hyV m₀).symm
    have h₁ := congrArg (fun z ↦ L (a ⊗ₜ z))
      (tensorObjStalkEquiv_symm_tmul_germ S E F (f y) V hyV m₁ n₀)
    have h₂ := (congrArg tR (stalkMap_pullbackStalkComparison_tmul_germ f φ (E ⊗ F)
        (Functor.OplaxMonoidal.δ P E F) y a V hyV _)).trans
      ((map_smul tR a _).trans (congrArg (a • ·)
        ((congrArg (fun s ↦ tR (germ (P.obj E ⊗ P.obj F).val.presheaf
          ((Opens.map f).obj V) y (Opens.mem_map.mpr hyV) s))
          (pullback_δ_val_app_unit_μ_tmul f φ E F V m₁ n₀)).trans
          (tensorObjStalkComparison_germ_μ_tmul R (P.obj E) (P.obj F) y ((Opens.map f).obj V)
            (Opens.mem_map.mpr hyV) _ _))))
    have he : tensorObjStalkComparison S E F (f y) (e (gE ⊗ₜ gF)) = gE ⊗ₜ gF :=
      (tensorObjStalkEquiv_apply S E F (f y) _).symm.trans
        ((tensorObjStalkEquiv S E F (f y)).apply_symm_apply _)
    have hM := (congrArg (fun z ↦ pMap (TensorProduct.AlgebraTensorModule.distribBaseChange
          ↑(stalk S.obj (f y)) ↑(stalk R.obj y) _ _ z))
        ((tensorObjStalkComparison S E F (f y)).baseChange_tmul a (e (gE ⊗ₜ gF)))).trans
      ((congrArg (fun z ↦ pMap (TensorProduct.AlgebraTensorModule.distribBaseChange
          ↑(stalk S.obj (f y)) ↑(stalk R.obj y) _ _ (a ⊗ₜ z))) he).trans
        ((congrArg pMap (TensorProduct.AlgebraTensorModule.distribBaseChange_tmul
          ↑(stalk S.obj (f y)) ↑(stalk R.obj y) gE gF a)).trans
          ((TensorProduct.map_tmul (pullbackStalkComparison f φ E y)
              (pullbackStalkComparison f φ F y) _ _).trans
            ((congrArg₂ (· ⊗ₜ ·) (pullbackStalkComparison_tmul_germ f φ E y a V hyV m₁)
              (pullbackStalkComparison_one_tmul_germ f φ F y V hyV n₀)).trans
              (TensorProduct.smul_tmul' a _ _)))))
    exact (congrArg (fun z ↦ L (a ⊗ₜ e z)) (congrArg₂ (· ⊗ₜ ·) hu' hv.symm)).trans
      ((h₁.trans h₂).trans (hM.symm.trans
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
    Function.Bijective (stalkMap (pullbackObjUnitToUnit φ) y) := by
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  let eR := ((unitStalkEquiv S (f y)).baseChange
      ↑(stalk S.obj (f y)) ↑(stalk R.obj y) _ _).trans
    (TensorProduct.AlgebraTensorModule.rid ↑(stalk S.obj (f y)) ↑(stalk R.obj y) ↑(stalk R.obj y))
  have hEq : ((unitStalkEquiv R y : _ → _) ∘
      (stalkMap (pullbackObjUnitToUnit φ) y : _ → _) ∘
        (pullbackStalkComparison f φ (unit (ringCatSheaf S)) y : _ → _)) = (eR : _ → _) :=
    congrArg DFunLike.coe
      (unitStalkEquiv_stalkMap_pullbackObjUnitToUnit_pullbackStalkComparison f φ y)
  have hbij : Function.Bijective ((unitStalkEquiv R y : _ → _) ∘
      (stalkMap (pullbackObjUnitToUnit φ) y : _ → _) ∘
        (pullbackStalkComparison f φ (unit (ringCatSheaf S)) y : _ → _)) := hEq.symm ▸ eR.bijective
  exact (Function.Bijective.of_comp_iff _
    (pullbackStalkComparison_bijective f φ (unit (ringCatSheaf S)) y)).mp
      ((Function.Bijective.of_comp_iff' (unitStalkEquiv R y).bijective _).mp hbij)

/-- At every point `y : Y`, the stalk map of `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` is bijective. -/
@[stacks 01CD]
theorem bijective_stalkMap_pullback_δ (E F : SheafOfModules.{u} (ringCatSheaf S)) (y : Y) :
    Function.Bijective (stalkMap (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) y) := by
  let _ : Algebra ↑(stalk S.obj (f y)) ↑(stalk R.obj y) := (stalkRingHom f φ y).hom.toAlgebra
  let eR := (((tensorObjStalkEquiv S E F (f y)).baseChange
      ↑(stalk S.obj (f y)) ↑(stalk R.obj y) _ _).trans
    (TensorProduct.AlgebraTensorModule.distribBaseChange
      ↑(stalk S.obj (f y)) ↑(stalk R.obj y) _ _)).trans
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
  have hEq : ((tensorObjStalkComparison R ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y :
      _ → _) ∘ (stalkMap (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) y : _ → _) ∘
        (pullbackStalkComparison f φ (E ⊗ F) y : _ → _)) = (eR : _ → _) :=
    congrArg DFunLike.coe hLin
  have hbij := hEq.symm ▸ eR.bijective
  exact (Function.Bijective.of_comp_iff _ (pullbackStalkComparison_bijective f φ (E ⊗ F) y)).mp
    ((Function.Bijective.of_comp_iff'
      (tensorObjStalkComparison_bijective R ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F) y)
      _).mp hbij)

/-- The canonical unit comparison `f^* 𝒪_X ⟶ 𝒪_Y` of module pullback is an isomorphism. -/
instance isIso_pullbackObjUnitToUnit : IsIso (pullbackObjUnitToUnit φ) :=
  (isIso_iff_stalkMap_bijective _).mpr (bijective_stalkMap_pullbackObjUnitToUnit f φ)

/-- The oplax unit comparison `η : f^* 𝒪_X ⟶ 𝒪_Y` of module pullback is an isomorphism. -/
instance isIso_pullback_η : IsIso (Functor.OplaxMonoidal.η (pullback.{u} φ)) :=
  (pullback_η φ).symm ▸ inferInstance

/-- The oplax tensor comparison `δ : f^* (E ⊗ F) ⟶ f^* E ⊗ f^* F` is an isomorphism for arbitrary
sheaves of modules `E` and `F`. -/
@[stacks 01CD] instance isIso_pullback_δ (E F : SheafOfModules.{u} (ringCatSheaf S)) :
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) :=
  (isIso_iff_stalkMap_bijective _).mpr (bijective_stalkMap_pullback_δ f φ E F)

/-- The canonical isomorphism `f^* 𝒪_X ≅ 𝒪_Y` for pullback of sheaves of modules. -/
def pullbackUnitIso : (pullback.{u} φ).obj (𝟙_ _) ≅ 𝟙_ _ := asIso (pullbackObjUnitToUnit φ)
@[simp] theorem pullbackUnitIso_hom : (pullbackUnitIso f φ).hom = pullbackObjUnitToUnit φ := (rfl)

/-- The canonical isomorphism `f^* (E ⊗ F) ≅ f^* E ⊗ f^* F` for arbitrary sheaves of modules. -/
@[stacks 01CD] def pullbackTensorIso (E F : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullback.{u} φ).obj (E ⊗ F) ≅ (pullback.{u} φ).obj E ⊗ (pullback.{u} φ).obj F :=
  asIso (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F)
@[simp] theorem pullbackTensorIso_hom (E F : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackTensorIso f φ E F).hom = Functor.OplaxMonoidal.δ (pullback.{u} φ) E F := (rfl)
theorem pullbackTensorIso_inv (E F : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackTensorIso f φ E F).inv = inv (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) := (rfl)

/-- Pullback of sheaves of modules along a morphism of ringed spaces is strong monoidal. -/
@[stacks 01CD] instance pullbackMonoidal : (pullback.{u} φ).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (pullback.{u} φ)
theorem pullback_μ (E F : SheafOfModules.{u} (ringCatSheaf S)) :
    Functor.LaxMonoidal.μ (pullback.{u} φ) E F =
      inv (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F) :=
  IsIso.eq_inv_of_hom_inv_id (Functor.Monoidal.δ_μ _ E F)
@[simp]
theorem pullback_ε : Functor.LaxMonoidal.ε (pullback.{u} φ) = inv (pullbackObjUnitToUnit φ) :=
  IsIso.eq_inv_of_inv_hom_id
    ((congrArg (_ ≫ ·) (pullback_η φ).symm).trans (Functor.Monoidal.ε_η _))

/-- Pullback of sheaves of modules along `(f, φ)` is strong symmetric monoidal. -/
instance pullbackBraided : (pullback.{u} φ).Braided where
  toMonoidal := pullbackMonoidal f φ
  braided E F := by
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F),
      ← cancel_mono (Functor.OplaxMonoidal.δ (pullback.{u} φ) F E),
      Functor.Monoidal.δ_μ_assoc, Category.assoc, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
    exact pullback_map_braiding_hom_comp_δ φ E F

/-- Strong monoidal structure on `pullback (𝟙 (ringCatSheaf S))` over `𝟭 (Opens X)`. -/
@[instance_reducible]
def pullbackIdMonoidal (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    (pullback.{u} (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology X)
      (S := ringCatSheaf S) (R := ringCatSheaf S) (F := 𝟭 (Opens X))
      (𝟙 (ringCatSheaf S))).Monoidal :=
  letI := pullbackOplaxMonoidal (S := S) (R := S) (F := 𝟭 (Opens X)) (𝟙 (ringCatSheaf S))
  let PId := pullback.{u} (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology X)
    (S := ringCatSheaf S) (R := ringCatSheaf S) (F := 𝟭 (Opens X)) (𝟙 (ringCatSheaf S))
  haveI : IsIso (Functor.OplaxMonoidal.η PId) := by
    dsimp only [PId]; rw [pullback_id_η S]; infer_instance
  haveI (E F : SheafOfModules.{u} (ringCatSheaf S)) : IsIso (Functor.OplaxMonoidal.δ PId E F) := by
    let gId := (pullbackId (ringCatSheaf S)).hom.app E ⊗ₘ (pullbackId (ringCatSheaf S)).hom.app F
    have : IsIso (Functor.OplaxMonoidal.δ PId E F ≫ gId) :=
      (pullback_id_δ S E F).symm ▸ inferInstance
    exact IsIso.of_isIso_comp_right (Functor.OplaxMonoidal.δ PId E F) gId
  Functor.Monoidal.ofOplaxMonoidal PId

/-- The canonical identity isomorphism `SheafOfModules.pullbackId` is monoidal. -/
theorem isMonoidal_pullbackId_hom (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    letI := pullbackIdMonoidal S
    NatTrans.IsMonoidal (pullbackId.{u} (ringCatSheaf S)).hom := by
  let _ := pullbackIdMonoidal S
  refine { unit := ?_, tensor := fun E F ↦ ?_ }
  · rw [Functor.LaxMonoidal.id_ε, ← pullback_id_η S]; exact Functor.Monoidal.ε_η _
  · rw [← cancel_epi (Functor.OplaxMonoidal.δ
        (pullback.{u} (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology X)
          (S := ringCatSheaf S) (R := ringCatSheaf S) (F := 𝟭 (Opens X)) (𝟙 (ringCatSheaf S))) E F),
      Functor.Monoidal.δ_μ_assoc, Functor.LaxMonoidal.id_μ, Category.comp_id]
    exact (pullback_id_δ S E F).symm
variable {Z : TopCat.{u}} (g : Z ⟶ Y)
  {T : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
  (ψ : ringCatSheaf R ⟶
    ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf T))
  [(pushforward.{u} ψ).IsRightAdjoint]

/-- Strong monoidal structure on pullback along `(φ, ψ)` over `Opens.map f ⋙ Opens.map g`. -/
@[instance_reducible] def pullbackCompTargetMonoidal :
    haveI := isRightAdjoint_pushforward_comp f φ g ψ
    (pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)).Monoidal :=
  haveI := isRightAdjoint_pushforward_comp f φ g ψ
  letI := pullbackOplaxMonoidal (F := Opens.map f ⋙ Opens.map g) (S := S) (R := T)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)
  haveI : IsIso (Functor.OplaxMonoidal.η
      (pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
        (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))) := by
    rw [pullback_comp_η φ ψ]; infer_instance
  haveI (E F : SheafOfModules.{u} (ringCatSheaf S)) :
      IsIso (Functor.OplaxMonoidal.δ
        (pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
          (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
            (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) E F) := by
    rw [pullback_comp_δ φ ψ E F]; infer_instance
  Functor.Monoidal.ofOplaxMonoidal _
private theorem pullbackComp_hom_tensor (E F : SheafOfModules.{u} (ringCatSheaf S)) :
    haveI := isRightAdjoint_pushforward_comp f φ g ψ
    letI := pullbackCompTargetMonoidal f φ g ψ
    Functor.LaxMonoidal.μ (pullback.{u} φ ⋙ pullback.{u} ψ) E F ≫
      (pullbackComp.{u} φ ψ).hom.app (E ⊗ F) =
      ((pullbackComp.{u} φ ψ).hom.app E ⊗ₘ (pullbackComp.{u} φ ψ).hom.app F) ≫
        Functor.LaxMonoidal.μ _ E F := by
  have := isRightAdjoint_pushforward_comp f φ g ψ
  let _ := pullbackCompTargetMonoidal f φ g ψ
  let δC := Functor.OplaxMonoidal.δ
    (pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ)) E F
  have : IsIso δC := by
    change IsIso (Functor.OplaxMonoidal.δ _ E F); rw [pullback_comp_δ φ ψ E F]; infer_instance
  apply (cancel_mono δC).mp
  let p₁ := Functor.LaxMonoidal.μ (pullback.{u} ψ) ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F)
  let p₂ := (pullback.{u} ψ).map (Functor.LaxMonoidal.μ (pullback.{u} φ) E F)
  let q₂ := (pullback.{u} ψ).map (Functor.OplaxMonoidal.δ (pullback.{u} φ) E F)
  let q₁ := Functor.OplaxMonoidal.δ (pullback.{u} ψ)
    ((pullback.{u} φ).obj E) ((pullback.{u} φ).obj F)
  let w := (pullbackComp.{u} φ ψ).hom.app E ⊗ₘ (pullbackComp.{u} φ ψ).hom.app F
  have hR : (w ≫ Functor.LaxMonoidal.μ _ E F) ≫ δC = w :=
    (Category.assoc _ _ δC).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_δ _ E F)).trans (Category.comp_id _))
  have hδ : (pullbackComp.{u} φ ψ).hom.app (E ⊗ F) ≫ δC = q₂ ≫ q₁ ≫ w :=
    (congrArg (_ ≫ ·) (pullback_comp_δ φ ψ E F)).trans
      (Iso.hom_inv_id_app_assoc (pullbackComp.{u} φ ψ) (E ⊗ F) _)
  have hp₂q₂ : p₂ ≫ q₂ = 𝟙 _ :=
    ((pullback.{u} ψ).map_comp _ _).symm.trans
      ((congrArg (pullback.{u} ψ).map (Functor.Monoidal.μ_δ (pullback.{u} φ) E F)).trans
        ((pullback.{u} ψ).map_id _))
  have hp₁q₁ : p₁ ≫ q₁ = 𝟙 _ := Functor.Monoidal.μ_δ (pullback.{u} ψ) _ _
  have hL₁ : (Functor.LaxMonoidal.μ (pullback.{u} φ ⋙ pullback.{u} ψ) E F ≫
      (pullbackComp.{u} φ ψ).hom.app (E ⊗ F)) ≫ δC = p₁ ≫ p₂ ≫ q₂ ≫ q₁ ≫ w :=
    (congrArg (fun m ↦ (m ≫ (pullbackComp.{u} φ ψ).hom.app (E ⊗ F)) ≫ δC)
      (Functor.LaxMonoidal.comp_μ _ _ E F)).trans
      ((Category.assoc (p₁ ≫ p₂) _ δC).trans
        ((Category.assoc p₁ p₂ _).trans (congrArg (p₁ ≫ p₂ ≫ ·) hδ)))
  have hL₂ : p₁ ≫ p₂ ≫ q₂ ≫ q₁ ≫ w = w :=
    (congrArg (p₁ ≫ ·) ((Category.assoc p₂ q₂ (q₁ ≫ w)).symm.trans
      ((congrArg (· ≫ (q₁ ≫ w)) hp₂q₂).trans (Category.id_comp _)))).trans
      ((Category.assoc p₁ q₁ w).symm.trans ((congrArg (· ≫ w) hp₁q₁).trans (Category.id_comp w)))
  exact (hL₁.trans hL₂).trans hR.symm

/-- The canonical composition isomorphism `SheafOfModules.pullbackComp` is monoidal. -/
theorem isMonoidal_pullbackComp_hom :
    haveI := isRightAdjoint_pushforward_comp f φ g ψ
    letI := pullbackCompTargetMonoidal f φ g ψ
    NatTrans.IsMonoidal (pullbackComp.{u} φ ψ).hom := by
  have := isRightAdjoint_pushforward_comp f φ g ψ
  let _ := pullbackCompTargetMonoidal f φ g ψ
  have : IsIso (Functor.OplaxMonoidal.η
      (pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
        (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))) := by
    rw [pullback_comp_η φ ψ]; infer_instance
  refine { unit := ?_, tensor := fun E F ↦ pullbackComp_hom_tensor f φ g ψ E F }
  rw [← cancel_mono (Functor.OplaxMonoidal.η
      (pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf T)
        (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).map ψ))),
    Category.assoc, Functor.Monoidal.ε_η, pullback_comp_η φ ψ, Iso.hom_inv_id_app_assoc,
    Functor.LaxMonoidal.comp_ε, Category.assoc, ← Functor.map_comp_assoc, Functor.Monoidal.ε_η,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.Monoidal.ε_η]
end SheafOfModules
end
