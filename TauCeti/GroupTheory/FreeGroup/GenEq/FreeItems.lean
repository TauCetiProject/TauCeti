/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Sort
public import TauCeti.GroupTheory.FreeGroup.GenEq.DeleteItems
public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism
public import TauCeti.GroupTheory.GroupAlgGeom.FreeVariables
import TauCeti.GroupTheory.GroupAlgGeom.ChangeOfCoordinates

/-!
# Free items of a generalised equation

An item of a generalised equation `Ω` is *free* when it belongs to no base, variable or constant
(`TauCeti.GenEq.IsFreeItem`). Deleting the free items gives the generalised equation
`\overline{Ω}` (`TauCeti.GenEq.deleteFreeItems`) of Kharlampovich–Myasnikov, §5.2 (before
Lemma 16). Since the free items occur in no equation, the system `Ω*` is, up to renaming the
items, the system `\overline{Ω}*` with the free items as further variables
(`TauCeti.GenEq.toSystem_eq_image_addFreeVars`). Hence the points of `Ω*` are the points of
`\overline{Ω}*` with arbitrary values of the free items
(`TauCeti.GenEq.mem_V_toSystem_iff_deleteFreeItems`).

The source's `F_{R(Ω)} = F_{R(\overline{Ω})} ∗ F(Y)`, `Y` the free items, holds for the groups
presented by the systems (`TauCeti.GroupAlgGeom.SystemGroup.addFreeVarsEquiv` for
`\overline{Ω}*` with the free variables `Y`). For coordinate groups there is only the surjection
`F_{R(\overline{Ω})} ∗ F(Y) → F_{R(\overline{Ω}*, Y)}` onto the coordinate group of
`\overline{Ω}*` with the free variables `Y`, which is that of `Ω*` up to renaming
(`TauCeti.GroupAlgGeom.CoordGroup.freeVarsHom`); it need not be injective.

## Main definitions

* `TauCeti.GenEq.freeItems`: the set of free items.
* `TauCeti.GenEq.deleteFreeItems`: the generalised equation `\overline{Ω}` without the free items.

## Main results

* `TauCeti.GenEq.toSystem_eq_image_addFreeVars`: `Ω*` is `\overline{Ω}*` with the free items as
  free variables, up to renaming.
* `TauCeti.GenEq.mem_V_toSystem_iff_deleteFreeItems`: the points of `Ω*` and of `\overline{Ω}*`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.2, D4.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open scoped Finset

variable {A : Type*} (Ω : GenEq A)

/-- The free items of a generalised equation: the items belonging to no base. -/
def freeItems : Finset (Fin Ω.numItems) :=
  {k | Ω.IsFreeItem k}

variable {Ω} in
@[simp]
theorem mem_freeItems {k : Fin Ω.numItems} : k ∈ Ω.freeItems ↔ Ω.IsFreeItem k := by
  simp [freeItems]

/-- No variable base contains a free item. -/
theorem disjoint_baseItems_freeItems (μ : Fin Ω.numBases) : Disjoint (Ω.baseItems μ) Ω.freeItems :=
  Finset.disjoint_left.2 fun _ hk hf => (Ω.isFreeItem_iff.1 (mem_freeItems.1 hf)).1 μ hk

/-- The generalised equation `\overline{Ω}` obtained from `Ω` by deleting its free items. -/
abbrev deleteFreeItems : GenEq A :=
  Ω.deleteItems Ω.freeItems Ω.disjoint_baseItems_freeItems

/-- The equations of `\overline{Ω}`, read in the items of `Ω`, are the equations of `Ω`: a free
item carries no constant base. -/
private theorem image_equations_deleteFreeItems :
    restoreEquation Ω.freeItems '' Ω.deleteFreeItems.equations = Ω.equations := by
  refine (image_equations_deleteItems_subset _).antisymm fun e he => ?_
  rcases equations_subset_union_deleteItems Ω.disjoint_baseItems_freeItems he with
    h | ⟨b, ⟨hb, hbS⟩, -⟩
  exacts [h, absurd (Ω.isConstantItem_iff.2 ⟨b, hb, rfl⟩)
    (Ω.isFreeItem_iff.1 (mem_freeItems.1 hbS)).2]

/-- Renaming the items of the relator `L R⁻¹` of an equation of `\overline{Ω}`, regarded as a word
in the remaining and the free items, gives the relator of the equation read in the items of `Ω`. -/
private theorem renameEquiv_inclFreeVars_toGX
    (u : List ((Fin #Ω.freeItemsᶜ ⊕ A) × Bool) × List ((Fin #Ω.freeItemsᶜ ⊕ A) × Bool)) :
    GX.renameEquiv (FreeGroup A)
        (finSumEquivOfFinset (s := Ω.freeItemsᶜ) rfl (congrArg Finset.card (compl_compl _)))
        (inclFreeVars _ _ (Fin #Ω.freeItems)
          (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk u.1 * (FreeGroup.mk u.2)⁻¹))) =
      EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (restoreEquation Ω.freeItems u).1 *
        (FreeGroup.mk (restoreEquation Ω.freeItems u).2)⁻¹) := by
  have h : ((GX.renameEquiv (FreeGroup A) (finSumEquivOfFinset (s := Ω.freeItemsᶜ) rfl
      (congrArg Finset.card (compl_compl _)))).toMonoidHom.comp
        (inclFreeVars _ _ (Fin #Ω.freeItems))).comp (EqIneqSystem.toGX _ FreeGroup.of) =
      (EqIneqSystem.toGX _ FreeGroup.of).comp
        (FreeGroup.map (Sum.map (Ω.freeItemsᶜ.orderEmbOfFin rfl) id)) :=
    FreeGroup.ext_hom _ _ fun x => by cases x <;> simp
  have := DFunLike.congr_fun h (FreeGroup.mk u.1 * (FreeGroup.mk u.2)⁻¹)
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at this
  rw [this, map_mul, map_inv, ← mk_restoreWord, ← mk_restoreWord, restoreEquation_fst,
    restoreEquation_snd]

/-- The system `Ω*` is, up to renaming the items, the system `\overline{Ω}*` of the generalised
equation without its free items, regarded as a system in the remaining items and the free items:
the remaining items keep their order, followed by the free items in their order. -/
theorem toSystem_eq_image_addFreeVars :
    Ω.toSystem = GX.renameEquiv (FreeGroup A)
        (finSumEquivOfFinset (s := Ω.freeItemsᶜ) rfl (congrArg Finset.card (compl_compl _))) ''
      addFreeVars (Fin #Ω.freeItems) Ω.deleteFreeItems.toSystem := by
  have h (Ω : GenEq A) : Ω.toSystem = (fun e => EqIneqSystem.toGX _ FreeGroup.of
      (FreeGroup.mk e.1 * (FreeGroup.mk e.2)⁻¹)) '' Ω.equations :=
    Set.ext fun _ => Ω.mem_toSystem_iff
  rw [h, h, addFreeVars_def, Set.image_image, Set.image_image,
    ← Ω.image_equations_deleteFreeItems, Set.image_image]
  exact Set.image_congr fun u _ => (Ω.renameEquiv_inclFreeVars_toGX u).symm

variable {Ω} in
/-- The points of `Ω*` are the points of the system of `Ω` without its free items, with
arbitrary values of the free items. -/
theorem mem_V_toSystem_iff_deleteFreeItems {H : Type*} [Group H] {ι : FreeGroup A →* H}
    {v : Fin Ω.numItems → H} :
    v ∈ V ι Ω.toSystem ↔ (fun k => v (Ω.freeItemsᶜ.orderEmbOfFin rfl k)) ∈
      V ι Ω.deleteFreeItems.toSystem := by
  rw [Ω.toSystem_eq_image_addFreeVars, mem_V_image_mulEquiv_iff ι _ (GX.renameEquiv_inl _),
    mem_V_addFreeVars]
  exact Iff.of_eq (congrArg (· ∈ V ι _) (funext fun k => by simp))

end GenEq

end TauCeti
