/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Stalks of sectionwise tensor products of presheaves of modules

For presheaves of modules `M`, `N` over a presheaf of commutative rings on a topological space,
this file constructs the canonical linear map from the stalk of their sectionwise tensor product
(Mathlib's `PresheafOfModulesOfCommRing.Monoidal.tensorObj`) to the tensor product of their
stalks over the ring stalk, and computes its values on germs of pure tensors.
The comparison is not asserted to be invertible.

## Main declarations

* `PresheafOfModules.tensorStalkComparison`: the comparison as a linear map over the ring stalk;
* `PresheafOfModules.tensorStalkComparison_germ_tmul`: its value on the germ of a pure tensor.
-/

public section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace PresheafOfModules

variable {X : TopCat.{u}}
  {R : X.Presheaf CommRingCat.{u}}
  (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) (x : X)

private abbrev tensorPresheaf :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u}) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj M N

-- Sections of `tensorObj M N` over `U` are by `rfl` the tensor product of the sections of `M`
-- and `N`; the identity cast `eqToHom (tensorObj_obj …)` records this identification.
private def tensorGermSemilinear (U : Opens X) (hx : x ∈ U) :
    (tensorPresheaf M N).obj (op U) →ₛₗ[(TopCat.Presheaf.germ R U x hx).hom]
      ↑(TopCat.Presheaf.stalk M.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R x)]
        ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  (TensorProduct.map (M.germSemilinear x U hx) (N.germSemilinear x U hx)).comp
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
  -- The cast `eqToHom (tensorObj_obj …)` in `tensorGermSemilinear` is the identity by `rfl`.
  change TensorProduct.map (M.germSemilinear x U hx) (N.germSemilinear x U hx) (m ⊗ₜ n) = _
  rw [TensorProduct.map_tmul, germSemilinear_apply, germSemilinear_apply]

private theorem tensorGermMap_res {U V : Opens X} (i : U ⟶ V) (hx : x ∈ U)
    (t : (tensorPresheaf M N).obj (op V)) :
    tensorGermMap M N x U hx ((tensorPresheaf M N).map i.op t) =
      tensorGermMap M N x V (i.le hx) t := by
  -- `TensorProduct.inductionOn` retypes `t` at the raw tensor product of the sections rather than
  -- at the carrier of `(tensorPresheaf M N).obj (op V)` (the two agree only up to the `rfl`
  -- identification `tensorObj_obj`), and the restriction appears as `ConcreteCategory.hom` rather
  -- than `ModuleCat.Hom.hom`; the rewrites below need `erw` to see through these wrappers.
  induction t using TensorProduct.inductionOn with
  | tmul m n =>
      erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul,
        tensorGermMap_tmul, tensorGermMap_tmul]
      have hm := TopCat.Presheaf.germ_res_apply M.presheaf i x hx m
      have hn := TopCat.Presheaf.germ_res_apply N.presheaf i x hx n
      -- `germ_res_apply` applies `M.presheaf.map` via `ConcreteCategory.hom`, while
      -- `presheaf_map_apply_coe` is stated with `AddCommGrpCat.Hom.hom`; `erw` unfolds the former.
      erw [PresheafOfModules.presheaf_map_apply_coe] at hm hn
      exact congrArg₂ (fun a b ↦ a ⊗ₜ b) hm hn
  | add a b ha hb =>
      erw [map_add, map_add, map_add, ha, hb]

private theorem tensorGermMap_smul (U : Opens X) (hx : x ∈ U)
    (r : R.obj (op U)) (t : (tensorPresheaf M N).obj (op U)) :
    tensorGermMap M N x U hx (r • t) =
      TopCat.Presheaf.germ R U x hx r • tensorGermMap M N x U hx t :=
  (tensorGermSemilinear M N x U hx).map_smul' r t

/-- The canonical map from the stalk of the sectionwise tensor product of two presheaves of modules
to the tensor product of their stalks. -/
def tensorStalkComparison :
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
theorem tensorStalkComparison_germ_tmul (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, CategoryTheory.Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj]
    (tensorStalkComparison M N x
        (TopCat.Presheaf.germ
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj M N).presheaf U x hx
          (m ⊗ₜ[R.obj (op U)] n)) =
      TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R x)]
        TopCat.Presheaf.germ N.presheaf U x hx n) :=
  ((PresheafOfModulesOfCommRing.Monoidal.tensorObj M N).stalkLiftCommRing_germ x
    (tensorGermMap M N x) (tensorGermMap_res M N x) (tensorGermMap_smul M N x) U hx _).trans
      (tensorGermMap_tmul M N x U hx m n)

end PresheafOfModules
