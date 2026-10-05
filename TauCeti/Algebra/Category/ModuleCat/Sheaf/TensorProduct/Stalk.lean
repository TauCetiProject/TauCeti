/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.TensorProduct.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

/-!
# Tensor products and stalks of sheaves of modules

This file constructs, over an arbitrary topological space and for arbitrary sheaves of modules
`M`, `N`, the canonical linear map from the stalk of their tensor product to the tensor product
of their stalks over the ring stalk, and computes its values on germs of sheafified pure tensors.
The comparison is not asserted to be invertible.

It is the sectionwise comparison `PresheafOfModules.tensorStalkComparison`, precomposed with
the inverse of the identification `PresheafOfModules.sheafificationStalkEquiv` of a stalk with
the stalk of the sheafification, and with the stalk map (`PresheafOfModules.stalkMapCommRing`)
of the defining isomorphism `tensorProductIso`.

## Main declarations

* `SheafOfModules.tensorStalkComparison`: the comparison as a linear map over the ring stalk;
* `SheafOfModules.tensorStalkComparison_apply`: its description as the composite above;
* `SheafOfModules.tensorStalkComparison_germ_unit_tmul`: its value on the germ of a sheafified
  pure tensor.
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (M N : SheafOfModules.{u} (ringCatSheaf R)) (x : X)

/-- The canonical linear map from the stalk of the tensor product of two sheaves of modules to
the tensor product of their stalks. -/
def tensorStalkComparison :
    ↑(TopCat.Presheaf.stalk (tensorProduct R M N).val.presheaf x) →ₗ[
      ↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  (PresheafOfModules.tensorStalkComparison M.val N.val x).comp
    (((PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val).sheafificationStalkEquiv
      R x).symm.toLinearMap.comp
        (PresheafOfModules.stalkMapCommRing (S := R.obj) x (tensorProductIso R M N).hom.val))

/-- The tensor stalk comparison is the sectionwise comparison, applied after transporting along
`tensorProductIso` and identifying the stalk of the sheafification with the original stalk. -/
theorem tensorStalkComparison_apply
    (s : ↑(TopCat.Presheaf.stalk (tensorProduct R M N).val.presheaf x)) :
    tensorStalkComparison R M N x s =
      PresheafOfModules.tensorStalkComparison M.val N.val x
        (((PresheafOfModulesOfCommRing.Monoidal.tensorObj M.val N.val).sheafificationStalkEquiv
          R x).symm
            (PresheafOfModules.stalkMapCommRing (S := R.obj) x
              (tensorProductIso R M N).hom.val s)) := by
  -- After unfolding, both sides are the same composite applied to `s`.
  unfold tensorStalkComparison
  rfl

/-- The tensor stalk comparison sends the germ of the pure tensor `m ⊗ₜ n`, pushed through the
sheafification unit and transported along `tensorProductIso`, to the tensor product of the
germs of `m` and `n`. -/
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
  rw [tensorStalkComparison_apply]
  -- `M.val`, `N.val` live over `(ringCatSheaf R).obj`, while the presheaf-level germ lemmas are
  -- stated over `R.obj ⋙ forget₂ CommRingCat RingCat`; the two agree only by unfolding
  -- `ringCatSheaf`, so these rewrites need `erw`.
  erw [PresheafOfModules.stalkMapCommRing_germ,
    ((_root_.SheafOfModules.evaluation _ (op U)).mapIso (tensorProductIso R M N)).inv_hom_id_apply,
    PresheafOfModules.sheafificationStalkEquiv_symm_germ_unit,
    PresheafOfModules.tensorStalkComparison_germ_tmul]
  -- The two sides differ only in writing the ring stalk via `(sheafToPresheaf _ _).obj R`,
  -- which is `R.obj` by definition.
  rfl

end SheafOfModules

end

end TauCeti
