/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Restriction maps of presheaves

Composing restriction maps along inclusions of opens in both directions gives the identity after
any morphism into the starting section object, since the inclusions force the opens to be equal.
Restricting a section twice along inclusions of opens is restricting it once, two proofs of the same
inclusion of opens give the same restriction map, and transporting a section along an equality of
open sets and restricting it is a single restriction.

## Main results

* `TopCat.Presheaf.comp_map_comp_map_eq_self`: composing restriction maps along inclusions in both
  directions gives the identity after any morphism into the starting section object.
* `TopCat.Presheaf.map_homOfLE_congr`: two proofs of the same inclusion of opens give the same
  restriction map.
* `TopCat.Presheaf.map_homOfLE_apply_map`: restricting a section twice along inclusions of opens is
  restricting it once.
* `TopCat.Presheaf.map_eqToHom_map_homOfLE`: transporting a section along an equality of open sets
  and restricting it is a single restriction.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Presheaf

universe w v u w'

variable {C : Type u} [Category.{v} C] {T : TopCat.{w}}

/-- Composing restriction maps along inclusions of opens in both directions gives the identity
after any morphism into the starting section object, since those inclusions force the opens to be
equal. The sections are given by a morphism `a` into `F.obj (op V)`, so that the lemma applies by
`exact` even when the intermediate open is only definitionally equal to the one in the composite. -/
theorem comp_map_comp_map_eq_self {F : T.Presheaf C} {A : C} {V V' : Opens T}
    (a : A ⟶ F.obj (op V)) (i : op V ⟶ op V') (j : op V' ⟶ op V) :
    (a ≫ F.map i) ≫ F.map j = a := by
  rw [Category.assoc, ← F.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _), F.map_id, Category.comp_id]

section Restriction

variable {FC : C → C → Type*} {CC : C → Type w'}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- Two proofs of the same inclusion of open sets give the same restriction map. -/
theorem map_homOfLE_congr {F : T.Presheaf C} {U V : Opens T} (h h' : U ≤ V)
    (s : ToType (F.obj (op V))) : F.map (homOfLE h).op s = F.map (homOfLE h').op s := by
  rw [Subsingleton.elim h h']

/-- Restricting a section twice along inclusions of open sets is restricting it once. -/
theorem map_homOfLE_apply_map {F : T.Presheaf C} {A B D : Opens T} (h₁ : A ≤ B) (h₂ : B ≤ D)
    (s : ToType (F.obj (op D))) :
    F.map (homOfLE h₁).op (F.map (homOfLE h₂).op s) = F.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, homOfLE_comp]

/-- Transporting a section along an equality of open sets and then restricting it is a single
restriction. -/
theorem map_eqToHom_map_homOfLE {F : T.Presheaf C} {A B D : Opens T} (e : A = B) (h : B ≤ D)
    (h' : A ≤ D) (s : ToType (F.obj (op D))) :
    F.map (eqToHom e).op (F.map (homOfLE h).op s) = F.map (homOfLE h').op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp,
    Subsingleton.elim (eqToHom e ≫ homOfLE h) (homOfLE h')]

end Restriction

end TopCat.Presheaf
