/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Enriched ordinary categories: basic lemmas

Let `C` be an ordinary category enriched over a monoidal category `V`.

* For a full subcategory `ObjectProperty.FullSubcategory P` of `C`, enriched hom objects,
  identities, and composition agree with those of `C`
  (`ObjectProperty.FullSubcategory.eHom_eq`, `ObjectProperty.FullSubcategory.eId_eq`,
  `ObjectProperty.FullSubcategory.eComp_eq`).
* When `V` is Cartesian monoidal, a morphism `f : a ⟶ b` of `C` gives, for every object `X` of `V`,
  the map `X ⟶ (a ⟶[V] b)` which is constant at `f`, namely `toUnit X ≫ eHomEquiv V f`. Enriched
  composition of two such constant maps is the constant map at the composite
  (`CategoryTheory.toUnit_eHomEquiv_tensorHom_comp_eComp`).

## Main declarations

* `CategoryTheory.ObjectProperty.FullSubcategory.eHom_eq`,
  `CategoryTheory.ObjectProperty.FullSubcategory.eId_eq`,
  `CategoryTheory.ObjectProperty.FullSubcategory.eComp_eq`: enriched hom objects, identities, and
  composition in a full subcategory are those of the underlying objects.
* `CategoryTheory.toUnit_eHomEquiv_tensorHom_comp_eComp`: enriched composition of the constant
  maps at `f` and `g` is the constant map at `f ≫ g`.
-/

public section

universe v' v u' u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

namespace ObjectProperty.FullSubcategory

section

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C] {P : ObjectProperty C}

/-- Enriched hom objects in a full subcategory are the enriched hom objects of the underlying
objects. -/
lemma eHom_eq (X Y : P.FullSubcategory) :
    (X ⟶[V] Y) = (X.obj ⟶[V] Y.obj) :=
  rfl

/-- Enriched identities in a full subcategory are the enriched identities of the underlying
objects. -/
@[reassoc]
lemma eId_eq (X : P.FullSubcategory) :
    eId V X = eId V X.obj :=
  rfl

/-- Enriched composition in a full subcategory is the enriched composition of the underlying
objects. -/
@[reassoc]
lemma eComp_eq (X Y Z : P.FullSubcategory) :
    eComp V X Y Z = eComp V X.obj Y.obj Z.obj :=
  rfl

end

end ObjectProperty.FullSubcategory

variable {V : Type u'} [Category.{v'} V] [CartesianMonoidalCategory V] {C : Type u}
  [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- Tensoring two maps which are constant at morphisms `f` and `g` and then composing gives the
map which is constant at `f ≫ g`. -/
@[reassoc]
lemma toUnit_eHomEquiv_tensorHom_comp_eComp {X Y : V} {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    ((toUnit X ≫ eHomEquiv V f) ⊗ₘ (toUnit Y ≫ eHomEquiv V g)) ≫ eComp V a b c =
      toUnit _ ≫ eHomEquiv V (f ≫ g) := by
  have : toUnit X ⊗ₘ toUnit Y = toUnit _ ≫ (λ_ (𝟙_ V)).inv :=
    CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (toUnit_unique _ _)
  rw [← tensorHom_comp_tensorHom_assoc, this, eHomEquiv_comp, Category.assoc]

end CategoryTheory
