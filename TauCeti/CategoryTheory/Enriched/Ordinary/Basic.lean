/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Constant maps into enriched hom-objects

Let `C` be an ordinary category enriched over a Cartesian monoidal category `V`. A morphism
`f : a ⟶ b` of `C` gives, for every object `X` of `V`, the map `X ⟶ (a ⟶[V] b)` which is constant
at `f`, namely `toUnit X ≫ eHomEquiv V f`. This file shows that enriched composition of two such
constant maps is the constant map at the composite.

## Main declarations

* `CategoryTheory.toUnit_eHomEquiv_tensorHom_comp_eComp`: enriched composition of the constant
  maps at `f` and `g` is the constant map at `f ≫ g`.
-/

public section

universe v' v u' u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

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
