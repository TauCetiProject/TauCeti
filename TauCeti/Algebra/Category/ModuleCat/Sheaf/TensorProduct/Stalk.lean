/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor products and stalks of sheaves of modules

This file constructs the canonical comparison from the stalk of a tensor product of sheaves of
modules to the tensor product of their stalks. It is characterized on germs of pure tensors.

The comparison is the stalkwise map underlying the compatibility of module pullback with tensor
products. It also provides the local calculation used to identify fibres of algebraic vector
bundles.

## Main declarations

* `PresheafOfModules.tensorPresheafStalkComparison`: the comparison before sheafification;
* `SheafOfModules.tensorStalkComparison`: the comparison for tensor products of module sheaves.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
  TopCat.Presheaf
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace PresheafOfModules

variable {X : TopCat.{u}}
  {R : X.Presheaf CommRingCat.{u}}
  (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) (x : X)

private def germSemilinear (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (U : Opens X) (hx : x ∈ U) :
    P.obj (op U) →ₛₗ[(TopCat.Presheaf.germ R U x hx).hom]
      ↑(TopCat.Presheaf.stalk P.presheaf x) where
  toFun := TopCat.Presheaf.germ P.presheaf U x hx
  map_add' := map_add _
  map_smul' r m := P.germ_smul x U hx r m

private abbrev tensorPresheaf :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u}) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj M N

private def tensorGermSemilinear (U : Opens X) (hx : x ∈ U) :
    (tensorPresheaf M N).obj (op U) →ₛₗ[(TopCat.Presheaf.germ R U x hx).hom]
      ↑(TopCat.Presheaf.stalk M.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R x)]
        ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  (TensorProduct.map (germSemilinear x M U hx) (germSemilinear x N U hx)).comp
    (eqToHom (PresheafOfModulesOfCommRing.Monoidal.tensorObj_obj M N (op U))).hom

private def tensorGermMap (U : Opens X) (hx : x ∈ U) :
    (tensorPresheaf M N).obj (op U) →+
      ↑(TopCat.Presheaf.stalk M.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R x)]
        ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  (tensorGermSemilinear M N x U hx).toAddMonoidHom

@[simp]
private theorem tensorGermMap_tmul (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    tensorGermMap M N x U hx (m ⊗ₜ[R.obj (op U)] n) =
      TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R x)]
        TopCat.Presheaf.germ N.presheaf U x hx n := by
  rfl

private theorem tensorGermMap_res {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (t : (tensorPresheaf M N).obj (op V)) :
    tensorGermMap M N x U hx ((tensorPresheaf M N).map i.op t) =
      tensorGermMap M N x V (i.le hx) t := by
  induction t using TensorProduct.inductionOn with
  | tmul m n =>
      erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul,
        tensorGermMap_tmul, tensorGermMap_tmul]
      have hm := TopCat.Presheaf.germ_res_apply M.presheaf i x hx m
      have hn := TopCat.Presheaf.germ_res_apply N.presheaf i x hx n
      erw [PresheafOfModules.presheaf_map_apply_coe] at hm hn
      exact congrArg₂ (fun a b ↦ a ⊗ₜ b) hm hn
  | add a b ha hb =>
      erw [map_add, map_add, map_add]
      exact congrArg₂ (fun s t ↦ s + t) ha hb

private theorem tensorGermMap_smul (U : Opens X) (hx : x ∈ U)
    (r : R.obj (op U)) (t : (tensorPresheaf M N).obj (op U)) :
    tensorGermMap M N x U hx (r • t) =
      TopCat.Presheaf.germ R U x hx r • tensorGermMap M N x U hx t :=
  (tensorGermSemilinear M N x U hx).map_smul' r t

/-- The canonical map from the stalk of the sectionwise tensor product of two presheaves of modules
to the tensor product of their stalks. -/
def tensorPresheafStalkComparison :
    ↑(TopCat.Presheaf.stalk
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj M N).presheaf x) →ₗ[
        ↑(TopCat.Presheaf.stalk R x)]
      ↑(TopCat.Presheaf.stalk M.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R x)]
        ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  (PresheafOfModulesOfCommRing.Monoidal.tensorObj M N).stalkLiftCommRing x
    (tensorGermMap M N x)
    (tensorGermMap_res M N x) (tensorGermMap_smul M N x)

/-- The sectionwise tensor stalk comparison sends the germ of a pure tensor to the tensor product
of the two germs. -/
@[simp]
theorem tensorPresheafStalkComparison_germ_tmul (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, CategoryTheory.Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj]
    (tensorPresheafStalkComparison M N x
        (TopCat.Presheaf.germ
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj M N).presheaf U x hx
          (m ⊗ₜ[R.obj (op U)] n)) =
      TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R x)]
        TopCat.Presheaf.germ N.presheaf U x hx n) := by
  erw [PresheafOfModules.stalkLiftCommRing_germ]
  rfl

end PresheafOfModules

namespace SheafOfModules

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (M N : SheafOfModules.{u} (ringCatSheaf R)) (x : X)

private def stalkMap {P Q : SheafOfModules.{u} (ringCatSheaf R)} (f : P ⟶ Q) :
    ↑(TopCat.Presheaf.stalk P.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk Q.val.presheaf x) :=
  P.val.stalkLiftCommRing (S := R.obj) x
    (fun U hx ↦ (TopCat.Presheaf.germ Q.val.presheaf U x hx).hom.comp
      (f.val.app (op U)).hom.toAddMonoidHom)
    (fun i hx m ↦
      (congrArg (fun t ↦ TopCat.Presheaf.germ Q.val.presheaf _ x hx t)
        (PresheafOfModules.naturality_apply f.val i.op m)).trans
          (TopCat.Presheaf.germ_res_apply Q.val.presheaf i x hx _))
    (fun U hx r m ↦
      (congrArg (fun t ↦ TopCat.Presheaf.germ Q.val.presheaf U x hx t)
        ((f.val.app (op U)).hom.map_smul r m)).trans
          (Q.val.germ_smul (R := R.obj) x U hx r _))

@[simp]
private theorem stalkMap_germ {P Q : SheafOfModules.{u} (ringCatSheaf R)} (f : P ⟶ Q)
    (U : Opens X) (hx : x ∈ U) (m : P.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe]
    (stalkMap R x f (TopCat.Presheaf.germ P.val.presheaf U x hx m) =
      TopCat.Presheaf.germ Q.val.presheaf U x hx (f.val.app (op U) m)) := by
  unfold stalkMap
  erw [PresheafOfModules.stalkLiftCommRing_germ]
  · rfl
  · intro U V i hx m
    exact (congrArg (fun t ↦ TopCat.Presheaf.germ Q.val.presheaf _ x hx t)
      (PresheafOfModules.naturality_apply f.val i.op m)).trans
        (TopCat.Presheaf.germ_res_apply Q.val.presheaf i x hx _)

/-- The canonical linear map from the stalk of the tensor product of two sheaves of modules to
the tensor product of their stalks. -/
def tensorStalkComparison :
    ↑(TopCat.Presheaf.stalk (tensorProduct R M N).val.presheaf x) →ₗ[
      ↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  (PresheafOfModules.tensorPresheafStalkComparison M.val N.val x).comp
    (((PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val).sheafificationStalkEquiv
      R x).symm.toLinearMap.comp (stalkMap R x (tensorProductIso R M N).hom))

/-- The tensor stalk comparison sends the germ of the sheafification of a pure tensor to the
tensor product of its two germs. -/
@[simp]
theorem tensorStalkComparison_germ_unit_tmul (U : Opens X) (hx : x ∈ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, CategoryTheory.Functor.id_obj,
      CategoryTheory.Functor.comp_obj]
    (tensorStalkComparison R M N x
        (TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx
          ((tensorProductIso R M N).inv.val.app (op U)
            (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
              (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[(R.obj).obj (op U)] n)))) =
      TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
        TopCat.Presheaf.germ N.val.presheaf U x hx n) := by
  have hsection :
      (tensorProductIso R M N).hom.val.app (op U)
          ((tensorProductIso R M N).inv.val.app (op U)
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (ringCatSheaf R).obj)).unit.app (M.val ⊗ N.val)).app (op U)
                (m ⊗ₜ[(R.obj).obj (op U)] n))) =
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringCatSheaf R).obj)).unit.app (M.val ⊗ N.val)).app (op U)
            (m ⊗ₜ[(R.obj).obj (op U)] n) := by
    have hmor := congrArg
      (fun f :
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj (M.val ⊗ N.val) ⟶
          (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj (M.val ⊗ N.val) ↦
            f.val.app (op U))
      (Iso.inv_hom_id (tensorProductIso R M N))
    have happ := congrArg
      (fun f ↦ f (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringCatSheaf R).obj)).unit.app (M.val ⊗ N.val)).app (op U)
          (m ⊗ₜ[(R.obj).obj (op U)] n))) hmor
    erw [ModuleCat.comp_apply, ModuleCat.id_apply] at happ
    exact happ
  unfold tensorStalkComparison
  change PresheafOfModules.tensorPresheafStalkComparison M.val N.val x
      (((PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val).sheafificationStalkEquiv
        R x).symm
        (stalkMap R x (tensorProductIso R M N).hom
          (TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf U x hx
            ((tensorProductIso R M N).inv.val.app (op U)
              (((PresheafOfModules.sheafificationAdjunction
                (𝟙 (ringCatSheaf R).obj)).unit.app (M.val ⊗ N.val)).app (op U)
                  (m ⊗ₜ[(R.obj).obj (op U)] n)))))) = _
  erw [stalkMap_germ]
  rw [hsection]
  erw [
    PresheafOfModules.sheafificationStalkEquiv_symm_germ_unit,
    PresheafOfModules.tensorPresheafStalkComparison_germ_tmul]
  rfl

end SheafOfModules

end

end TauCeti
