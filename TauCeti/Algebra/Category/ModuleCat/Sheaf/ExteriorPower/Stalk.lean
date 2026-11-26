/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Stalks of exterior powers of sheaves of modules

The stalk of a sheaf exterior power is the exterior power of the stalk over the ring stalk.
The equivalence sends the germ of a sheafified wedge to the wedge of the germs of its factors.
It combines `PresheafOfModules.exteriorPowerStalkEquiv` with invariance under sheafification.

## References

* [The Stacks Project, Lemma 17.21.2](https://stacks.math.columbia.edu/tag/01CH).
-/

public section

open CategoryTheory Opposite TopologicalSpace TopCat.Presheaf
open TauCeti.SheafOfModules (ringCatSheaf)

universe u

noncomputable section

namespace SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (M : SheafOfModules.{u} (ringCatSheaf R)) (x : X) (n : ℕ)

/-- The stalk of the `n`-th exterior power of a sheaf of modules is canonically the
`n`-th exterior power of its stalk. -/
def exteriorPowerStalkEquiv :
    ↑(stalk ((exteriorPower R n).obj M).val.presheaf x) ≃ₗ[↑(stalk R.obj x)]
      ⋀[↑(stalk R.obj x)]^n ↑(stalk M.val.presheaf x) :=
  let e := PresheafOfModules.stalkLinearEquivCommRing (S := R.obj) x
    ((forget (ringCatSheaf R)).mapIso (exteriorPowerIso n M))
  let P := (PresheafOfModulesOfCommRing.exteriorPower n).obj M.val
  e ≪≫ₗ (P.sheafificationStalkEquiv R x).symm ≪≫ₗ M.val.exteriorPowerStalkEquiv x n

/-- Under the stalk equivalence, the wedge of germs with representatives on a common open
is represented by the sheafified wedge of those sections. -/
@[simp]
theorem exteriorPowerStalkEquiv_symm_ιMulti_germ (U : Opens X) (hx : x ∈ U)
    (m : Fin n → M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, sheafCompose_obj_obj, Functor.id_obj]
    ((M.exteriorPowerStalkEquiv x n).symm
        (exteriorPower.ιMulti ↑(stalk R.obj x) n
          (fun i ↦ germ M.val.presheaf U x hx (m i))) =
      germ ((exteriorPower R n).obj M).val.presheaf U x hx
        ((exteriorPowerIso n M).inv.val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
            ((PresheafOfModulesOfCommRing.exteriorPower n).obj M.val)).app (op U)
              (ModuleCat.exteriorPower.mk
                (M := PresheafOfModulesOfCommRing.obj (R := R.obj) M.val (op U)) m)))) := by
  let P := (PresheafOfModulesOfCommRing.exteriorPower n).obj M.val
  let e := (forget (ringCatSheaf R)).mapIso (exteriorPowerIso n M)
  let eStalk := PresheafOfModules.stalkLinearEquivCommRing (S := R.obj) x e
  let w : P.obj (op U) := ModuleCat.exteriorPower.mk
    (M := PresheafOfModulesOfCommRing.obj (R := R.obj) M.val (op U)) m
  let s := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringCatSheaf R).obj)).unit.app P).app (op U) w
  have h₁ := M.val.exteriorPowerStalkEquiv_symm_ιMulti_germ x n U hx m
  have h₂ := P.sheafificationStalkEquiv_germ R x U hx w
  have h₃ := PresheafOfModules.stalkMapCommRing_germ (S := R.obj) x e.inv U hx s
  exact (congrArg (fun t ↦ eStalk.symm (P.sheafificationStalkEquiv R x t)) h₁).trans
    ((congrArg eStalk.symm h₂).trans
      ((PresheafOfModules.stalkLinearEquivCommRing_symm_apply x e _).trans h₃))

/-- The stalk equivalence sends the germ of a sheafified wedge to the wedge of its germs. -/
@[simp]
theorem exteriorPowerStalkEquiv_germ_mk (U : Opens X) (hx : x ∈ U)
    (m : Fin n → M.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, sheafCompose_obj_obj, Functor.id_obj]
    (M.exteriorPowerStalkEquiv x n
        (germ ((exteriorPower R n).obj M).val.presheaf U x hx
          ((exteriorPowerIso n M).inv.val.app (op U)
            (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
              ((PresheafOfModulesOfCommRing.exteriorPower n).obj M.val)).app (op U)
                (ModuleCat.exteriorPower.mk
                  (M := PresheafOfModulesOfCommRing.obj (R := R.obj) M.val (op U)) m)))) =
      exteriorPower.ιMulti (↑(stalk R.obj x)) n (fun i ↦ germ M.val.presheaf U x hx (m i))) :=
  ((M.exteriorPowerStalkEquiv x n).symm_apply_eq.mp
    (M.exteriorPowerStalkEquiv_symm_ιMulti_germ x n U hx m)).symm

end SheafOfModules
