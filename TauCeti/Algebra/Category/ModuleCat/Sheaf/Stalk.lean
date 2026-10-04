/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Module structures on stalks of sheaves of modules

The stalk of a sheaf of modules over a sheaf of rings is a module over the ring stalk.
For commutative coefficient rings, it also retains the module action
of the original commutative ring stalk when the coefficient sheaf forgets commutativity.
The instance `SheafOfModules.stalkModule` exposes Mathlib's commutative presheaf stalk module
structure independently of the internal Hom construction. For ordinary ring coefficients,
Mathlib's presheaf stalk instance applies directly to the underlying presheaf of modules.

The linear equivalence `PresheafOfModules.sheafificationStalkEquiv` identifies a module
presheaf stalk with its sheafification stalk, preserving the original commutative-ring
stalk as coefficient ring. Its forward and inverse maps are characterized on germs.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf

universe u

noncomputable section

namespace SheafOfModules

variable {X : TopCat.{u}}

variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The stalk of a sheaf of modules carries Mathlib's module structure over the stalk of
the original commutative-ring sheaf. The carrier and action are unchanged by forgetting
commutativity in the coefficient sheaf. -/
instance stalkModule (P : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R)) (x : X) :
    Module ↑(TopCat.Presheaf.stalk R.obj x) ↑(TopCat.Presheaf.stalk P.val.presheaf x) :=
  let Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u}) := P.val
  inferInstanceAs (Module ↑(TopCat.Presheaf.stalk R.obj x)
    ↑(TopCat.Presheaf.stalk Q.presheaf x))

end SheafOfModules

namespace PresheafOfModules

variable {X : TopCat.{u}} (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (P : PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat.{u})) (x : X)

private abbrev sheafified :=
  (sheafification (R := TauCeti.SheafOfModules.ringCatSheaf S)
    (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).obj P

private def sheafificationUnit : P ⟶ (sheafified S P).val :=
  (sheafificationAdjunction (R := TauCeti.SheafOfModules.ringCatSheaf S)
    (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).unit.app P

private def sheafificationStalkMap :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) P.presheaf x) →ₗ[
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) S.obj x]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        (sheafified S P).val.presheaf x) :=
  P.stalkLiftCommRing (S := S.obj) x
    (fun U hx ↦ (TopCat.Presheaf.germ (sheafified S P).val.presheaf U x hx).hom.comp
      ((sheafificationUnit S P).app (op U)).hom.toAddMonoidHom)
    (fun i hx m ↦
      (congrArg (fun t ↦ TopCat.Presheaf.germ (sheafified S P).val.presheaf _ x hx t)
        (naturality_apply (sheafificationUnit S P) i.op m)).trans
          (TopCat.Presheaf.germ_res_apply (sheafified S P).val.presheaf i x hx _))
    (fun U hx r m ↦
      (congrArg (fun t ↦ TopCat.Presheaf.germ (sheafified S P).val.presheaf U x hx t)
        (((sheafificationUnit S P).app (op U)).hom.map_smul r m)).trans
          ((sheafified S P).val.germ_smul (R := S.obj) x U hx r _))

private lemma sheafificationStalkMap_germ (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    sheafificationStalkMap S P x (TopCat.Presheaf.germ P.presheaf U x hx m) =
      TopCat.Presheaf.germ (sheafified S P).val.presheaf U x hx
        ((sheafificationUnit S P).app (op U) m) :=
  by
    unfold sheafificationStalkMap
    erw [stalkLiftCommRing_germ]
    · rfl
    · intro U V i hx m
      exact (congrArg (fun t ↦ TopCat.Presheaf.germ (sheafified S P).val.presheaf _ x hx t)
        (naturality_apply (sheafificationUnit S P) i.op m)).trans
          (TopCat.Presheaf.germ_res_apply (sheafified S P).val.presheaf i x hx _)

private lemma sheafificationStalkMap_bijective :
    Function.Bijective (sheafificationStalkMap S P x) := by
  have h : (sheafificationStalkMap S P x :
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) P.presheaf x) →
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
          (sheafified S P).val.presheaf x)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((toPresheaf _).map (sheafificationUnit S P)) := by
    funext m
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf m
    erw [sheafificationStalkMap_germ, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  rw [h]
  have hunit : (toPresheaf _).map (sheafificationUnit S P) =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    exact toPresheaf_map_sheafificationAdjunction_unit_app
      (R := TauCeti.SheafOfModules.ringCatSheaf S)
      (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj) P
  erw [hunit]
  have hIso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    P.presheaf
  exact (ConcreteCategory.isIso_iff_bijective _).mp hIso

/-- Sheafification preserves module stalks, linearly over the original commutative-ring stalk.
The equivalence is induced by the unit of the sheafification adjunction. -/
def sheafificationStalkEquiv :
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) P.presheaf x) ≃ₗ[
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) S.obj x]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        ((sheafification (R := TauCeti.SheafOfModules.ringCatSheaf S)
          (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).obj P).val.presheaf x) :=
  LinearEquiv.ofBijective (sheafificationStalkMap S P x)
    (sheafificationStalkMap_bijective S P x)

/-- The sheafification stalk equivalence sends a germ to the germ of its unit image. -/
@[simp]
theorem sheafificationStalkEquiv_germ (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    dsimp% only [presheaf_obj_coe, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (P.sheafificationStalkEquiv S x (TopCat.Presheaf.germ P.presheaf U x hx m) =
      TopCat.Presheaf.germ
        ((sheafification (R := TauCeti.SheafOfModules.ringCatSheaf S)
          (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).obj P).val.presheaf U x hx
          (((sheafificationAdjunction
            (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).unit.app P).app (op U) m)) :=
  sheafificationStalkMap_germ S P x U hx m

/-- The inverse equivalence sends the germ of a unit image back to its original germ. -/
@[simp]
theorem sheafificationStalkEquiv_symm_germ_unit
    (U : Opens X) (hx : x ∈ U) (m : P.obj (op U)) :
    dsimp% only [presheaf_obj_coe, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    ((P.sheafificationStalkEquiv S x).symm
      (TopCat.Presheaf.germ
        ((sheafification (R := TauCeti.SheafOfModules.ringCatSheaf S)
          (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).obj P).val.presheaf U x hx
          (((sheafificationAdjunction
            (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).unit.app P).app (op U) m)) =
      TopCat.Presheaf.germ P.presheaf U x hx m) := by
  exact (P.sheafificationStalkEquiv S x).symm_apply_eq.mpr
    (P.sheafificationStalkEquiv_germ S x U hx m).symm

end PresheafOfModules
