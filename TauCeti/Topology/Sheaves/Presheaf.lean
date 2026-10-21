/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Restriction maps of presheaves

Composing restriction maps along inclusions of opens in both directions gives the identity after
any morphism into the starting section object, since the inclusions force the opens to be equal.
A family of sections over opens is compatible as soon as any two of its sections are restrictions
of a common section in the family.

## Main results

* `TopCat.Presheaf.comp_map_comp_map_eq_self`: composing restriction maps along inclusions in both
  directions gives the identity after any morphism into the starting section object.
* `TopCat.Presheaf.isCompatible_of_directed`: a family of sections, any two of which are
  restrictions of a common member, is compatible.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Presheaf

universe w v u

variable {C : Type u} [Category.{v} C] {T : TopCat.{w}}

/-- Composing restriction maps along inclusions of opens in both directions gives the identity
after any morphism into the starting section object, since those inclusions force the opens to be
equal. The sections are given by a morphism `a` into `F.obj (op V)`, so that the lemma applies by
`exact` even when the intermediate open is only definitionally equal to the one in the composite. -/
theorem comp_map_comp_map_eq_self {F : T.Presheaf C} {A : C} {V V' : Opens T}
    (a : A ⟶ F.obj (op V)) (i : op V ⟶ op V') (j : op V' ⟶ op V) :
    (a ≫ F.map i) ≫ F.map j = a := by
  rw [Category.assoc, ← F.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _), F.map_id, Category.comp_id]

/-- A family of sections over a directed family of opens is compatible as soon as any two of its
sections are restrictions of a common section in the family. -/
theorem isCompatible_of_directed {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {F : Presheaf C T}
    {ι : Type*} {U : ι → Opens T} {sf : ∀ i, ToType (F.obj (op (U i)))}
    (h : ∀ i j, ∃ k, ∃ (hik : U i ≤ U k) (hjk : U j ≤ U k),
      F.map (homOfLE hik).op (sf k) = sf i ∧ F.map (homOfLE hjk).op (sf k) = sf j) :
    IsCompatible F U sf := by
  intro i j
  obtain ⟨k, hik, hjk, hi, hj⟩ := h i j
  rw [← hi, ← hj, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp,
    ← F.map_comp]
  rfl

end TopCat.Presheaf
