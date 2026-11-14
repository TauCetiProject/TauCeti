/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic

/-!
# Port lists and word projection on the free monoidal category

An object of Mathlib's `CategoryTheory.FreeMonoidalCategory C` is a parenthesized formal tensor
word built from generators `of a`, the formal unit `unit`, and formal binary tensor products.
Forgetting parenthesizations and formal units yields the ordered list `toList` of generating
letters (ports) of the word: `of a` has port list `[a]`, the unit word has port list `[]`, and
`X ⊗ Y` concatenates the port lists of `X` and `Y`.

Every morphism in `FreeMonoidalCategory C` (built from identities, associators, and unitors)
preserves `toList` (`toList_eq_of_hom`). In particular, inserting or deleting formal units does
not change the port list or port count, while tensoring generators adds their port counts.

This file also records computation, identity, and composition rules for
`FreeMonoidalCategory.projectObj`, together with how `toList` interacts with word substitution
via `projectObj` (`toList_projectObj`).

## References

* `Mathlib/CategoryTheory/Monoidal/Free/Basic.lean` (Markus Himmel).
-/

public section

universe u u' u'' v'

namespace CategoryTheory.FreeMonoidalCategory

open MonoidalCategory

variable {C : Type u}

section ProjectObj

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

@[simp]
theorem projectObj_of (f : C → D) (a : C) : projectObj f (of a) = f a := rfl

@[simp]
theorem projectObj_unit (f : C → D) :
    projectObj f (𝟙_ (FreeMonoidalCategory C)) = 𝟙_ D := rfl

@[simp]
theorem projectObj_tensor (f : C → D) (X Y : FreeMonoidalCategory C) :
    projectObj f (X ⊗ Y) = projectObj f X ⊗ projectObj f Y := rfl

/-- Interpreting the generators of `FreeMonoidalCategory C` as themselves acts as the identity on
every formal tensor word. -/
@[simp]
theorem projectObj_of_self (X : FreeMonoidalCategory C) :
    projectObj (of : C → FreeMonoidalCategory C) X = X := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor _ _ hX hY => simp [hX, hY]

/-- Interpreting a formal tensor word along a map into `FreeMonoidalCategory C'` and then into a
monoidal category `D` agrees with interpreting directly by the composite generator assignment. -/
theorem projectObj_projectObj {C' : Type u''} (f : C → FreeMonoidalCategory C') (g : C' → D)
    (X : FreeMonoidalCategory C) :
    projectObj g (projectObj f X) = projectObj (fun a ↦ projectObj g (f a)) X := by
  induction X with
  | of _ => rfl
  | unit => rfl
  | tensor _ _ hX hY => simp [hX, hY]

end ProjectObj

/-- The ordered list of generating objects (ports) appearing in a formal tensor word, forgetting
parenthesizations and formal tensor units. -/
def toList : FreeMonoidalCategory C → List C
  | .of a => [a]
  | .unit => []
  | .tensor X Y => X.toList ++ Y.toList

@[simp]
theorem toList_of (a : C) : (of a).toList = [a] := (rfl)

@[simp]
theorem toList_unit : (𝟙_ (FreeMonoidalCategory C)).toList = [] := (rfl)

@[simp]
theorem toList_tensor (X Y : FreeMonoidalCategory C) : (X ⊗ Y).toList = X.toList ++ Y.toList :=
  (rfl)

/-- Structural morphisms in `FreeMonoidalCategory C` preserve the ordered list of generating
ports. -/
theorem toList_eq_of_hom {X Y : FreeMonoidalCategory C} (f : X ⟶ Y) : X.toList = Y.toList := by
  induction f using Hom.inductionOn with
  | id => rfl
  | α_hom => simp [List.append_assoc]
  | α_inv => simp [List.append_assoc]
  | l_hom => simp
  | l_inv => simp
  | ρ_hom => simp
  | ρ_inv => simp
  | comp _ _ hf hg => exact hf.trans hg
  | whiskerLeft _ _ hf => simp [hf]
  | whiskerRight _ _ hf => simp [hf]

/-- Substituting a formal tensor word for each generator replaces each port in `X.toList` by the
port list of its assigned word. -/
@[simp]
theorem toList_projectObj {D : Type u'} (f : C → FreeMonoidalCategory D)
    (X : FreeMonoidalCategory C) :
    (projectObj f X).toList = X.toList.flatMap (fun a ↦ (f a).toList) := by
  induction X with
  | of => simp
  | unit => simp
  | tensor _ _ hX hY => simp [hX, hY, List.flatMap_append]

end CategoryTheory.FreeMonoidalCategory
