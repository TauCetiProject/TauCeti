/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.LocallyInduced
public import TauCeti.CategoryTheory.DoubleCategory.Representation.Basic
public import TauCeti.CategoryTheory.DoubleCategory.Bicategory

/-!
# The bicategory of represented generators

A horizontal representation of a path double category induces a bicategory on its generating
arrows. Its hom-categories are the singleton globular hom-categories, composition is the chosen
binary composite, and the identity is the chosen nullary composite. Whiskering and coherence
are obtained by pasting in the strict path bicategory and conjugating by the chosen comparison
isomorphisms. In particular the triangle and pentagon laws are consequences of the strict
double-category laws, rather than additional assumptions on a representation.

The singleton inclusion is a pseudofunctor, locally the previously constructed equivalence of
hom-categories. The same construction applied to the transpose gives the vertical bicategory.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; Definitions 3.1–3.3 and Remark 3.5.
-/

public section

universe s u h v

namespace TauCeti.StrictDoubleCategory

open CategoryTheory
open scoped Bicategory

variable {O : Type u} {H : Quiver.{h} O} {V : Category.{v} O}
  {D : StrictDoubleCategory.{s} O (pathCategory O H) V}

namespace HorizontalRepresentation

variable (R : D.HorizontalRepresentation)

/-- The chosen composites of horizontal generators, with their comparisons in the strict
path bicategory. The body is exposed so that the induced 1-cell and 2-cell types compute as
generators and singleton globular cells. -/
@[expose, simps obj map unit mul mapUnit mapMul]
def inductionData : BicategoryInductionData D.HorizontalBicategory O H where
  obj a := ⟨a⟩
  map f := ⟨@Quiver.Hom.toPath O H _ _ f⟩
  unit := R.unit
  mul := R.mul
  mapUnit a := (R.unitIso a).symm
  mapMul f g := (R.mulIso f g).symm

/-- The horizontal bicategory on generators of a represented path double category.
Its 2-cells are horizontal globular cells between singleton paths. -/
abbrev GeneratorBicategory := R.inductionData.Obj

/-- Singleton inclusion from represented generators into the strict path bicategory.
It preserves composition and identities through the chosen representation isomorphisms. -/
abbrev singletonPseudofunctor : R.GeneratorBicategory ⥤ᵖ D.HorizontalBicategory :=
  R.inductionData.inclusion

/-- On each hom-category singleton inclusion is the original fully faithful singleton functor.
The equivalence `R.homEquivalence` therefore supplies its explicit inverse. -/
theorem singletonPseudofunctor_mapFunctor (a b : R.GeneratorBicategory) :
    R.singletonPseudofunctor.mapFunctor a b = D.singletonFunctor a.obj b.obj :=
  (rfl)

variable {R} {a b c : R.GeneratorBicategory}

/-- Left whiskering agrees with the existing represented composition bifunctor. -/
theorem generatorBicategory_whiskerLeft (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') :
    f ◁ η = (R.compFunctor a.obj b.obj c.obj).map (Prod.mkHom (𝟙 f) η) := by
  apply InducedCategory.hom_ext
  -- The induced hom-category and the original generator category have identical morphisms.
  erw [compFunctor_map_hom]
  rfl

/-- Right whiskering agrees with the existing represented composition bifunctor. -/
theorem generatorBicategory_whiskerRight {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) :
    η ▷ g = (R.compFunctor a.obj b.obj c.obj).map (Prod.mkHom η (𝟙 g)) := by
  apply InducedCategory.hom_ext
  -- The induced hom-category and the original generator category have identical morphisms.
  erw [compFunctor_map_hom]
  rfl

end HorizontalRepresentation

end TauCeti.StrictDoubleCategory
