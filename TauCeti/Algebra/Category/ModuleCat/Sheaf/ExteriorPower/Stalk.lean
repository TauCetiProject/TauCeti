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
The equivalence is natural in the module sheaf and sends the germ of a sheafified wedge to the
wedge of the germs of its factors.
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
        (M.exteriorPowerMk (R := R) (op U) m)) := by
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
          (M.exteriorPowerMk (R := R) (op U) m)) =
      exteriorPower.ιMulti (↑(stalk R.obj x)) n (fun i ↦ germ M.val.presheaf U x hx (m i))) :=
  ((M.exteriorPowerStalkEquiv x n).symm_apply_eq.mp
    (M.exteriorPowerStalkEquiv_symm_ιMulti_germ x n U hx m)).symm

/-- The exterior-power stalk equivalence is natural in the module sheaf. -/
theorem exteriorPowerStalkEquiv_naturality
    {N : SheafOfModules.{u} (ringCatSheaf R)} (g : M ⟶ N) :
    (N.exteriorPowerStalkEquiv x n).toLinearMap ∘ₗ
        PresheafOfModules.stalkMapCommRing (S := R.obj) x ((exteriorPower R n).map g).val =
      exteriorPower.map n (PresheafOfModules.stalkMapCommRing (S := R.obj) x g.val) ∘ₗ
        (M.exteriorPowerStalkEquiv x n).toLinearMap := by
  let E := PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n
  let eM := (forget (ringCatSheaf R)).mapIso (exteriorPowerIso n M)
  let eN := (forget (ringCatSheaf R)).mapIso (exteriorPowerIso n N)
  let pM := (E.obj M.val).sheafificationStalkEquiv R x
  let pN := (E.obj N.val).sheafificationStalkEquiv R x
  let d := PresheafOfModules.stalkMapCommRing (S := R.obj) x
    ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map (E.map g.val)).val
  -- The stalk equivalence uses the sheaf module structure, whereas the stalk map
  -- uses the definitionally equal module structure from the underlying presheaf.
  erw [exteriorPower_map (R := R), comp_val, comp_val,
    PresheafOfModules.stalkMapCommRing_comp, PresheafOfModules.stalkMapCommRing_comp]
  apply LinearMap.ext
  intro t
  let s := pM.symm (PresheafOfModules.stalkLinearEquivCommRing (S := R.obj) x eM t)
  have hu := LinearMap.congr_fun
    ((E.obj M.val).sheafificationStalkEquiv_naturality R x (E.map g.val)) s
  have hp := LinearMap.congr_fun (M.val.exteriorPowerStalkEquiv_naturality x n g.val) s
  -- Evaluate the composites through the stalk maps of the defining isomorphisms.
  unfold exteriorPowerStalkEquiv
  change N.val.exteriorPowerStalkEquiv x n
      (pN.symm (PresheafOfModules.stalkLinearEquivCommRing (S := R.obj) x eN
        (PresheafOfModules.stalkMapCommRing (S := R.obj) x eN.inv
          (d (PresheafOfModules.stalkMapCommRing (S := R.obj) x eM.hom t))))) =
    exteriorPower.map n (PresheafOfModules.stalkMapCommRing (S := R.obj) x g.val)
      (M.val.exteriorPowerStalkEquiv x n s)
  -- The inverse formula presents the stalk through the forgetful functor.
  erw [← PresheafOfModules.stalkLinearEquivCommRing_symm_apply x eN,
    LinearEquiv.apply_symm_apply]
  -- Evaluate the naturality equation on the chosen preimage under sheafification.
  change pN (PresheafOfModules.stalkMapCommRing (S := R.obj) x (E.map g.val) s) = d (pM s) at hu
  have hM : pM s = PresheafOfModules.stalkMapCommRing (S := R.obj) x eM.hom t :=
    (pM.apply_symm_apply _).trans (PresheafOfModules.stalkLinearEquivCommRing_apply x eM t)
  rw [← hM, ← hu, LinearEquiv.symm_apply_apply]
  exact hp

end SheafOfModules
