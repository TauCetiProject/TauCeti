/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution
public import Mathlib.CategoryTheory.Localization.LocallySmall

/-!
# Small morphism types in unbounded derived categories

The derived category of a Grothendieck abelian category has morphism types in the universe
relative to which the category is Grothendieck abelian. This universe can be smaller than
both the universe of its objects and the universe of its original morphism types.

The more general ingredient is that K-injective resolutions preserve local smallness on
passing to the derived category: the fully faithful K-injective replacement functor embeds
its morphism types into those of the homotopy category. That category is locally small
because its morphisms are quotients of morphisms of complexes.

`CategoryTheory.IsGrothendieckAbelian.hasDerivedCategory` chooses the small-Hom derived
category using Mathlib's `MorphismProperty.hasLocalizationOfLocallySmall`. In particular,
derived categories of module sheaves can use the universe of the site and coefficients,
rather than the larger universe of the category of sheaves. This choice does not change
which maps are inverted: `DerivedCategory.Q` is still the localization at all
quasi-isomorphisms, without any boundedness assumption.

## References

* M. Hovey, *Model category structures on chain complexes of sheaves*, Theorem 2.2.
* J. Lurie, *Higher Algebra*, §1.3.5.
-/

public section

open CategoryTheory

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The localization of unbounded cochain complexes in a Grothendieck abelian category at
quasi-isomorphisms is locally small in the universe relative to which the category is
Grothendieck abelian. -/
theorem locallySmall_localization_quasiIso :
    LocallySmall.{w} (HomologicalComplex.quasiIso C (.up ℤ)).Localization := by
  let := HasDerivedCategory.standard C
  exact inferInstanceAs (LocallySmall.{w} (DerivedCategory C))

/-- The unbounded derived category of a Grothendieck abelian category, with morphism types
in the universe relative to which the category is Grothendieck abelian. -/
noncomputable instance hasDerivedCategory : HasDerivedCategory.{w} C := by
  letI := locallySmall_localization_quasiIso C
  exact (HomologicalComplex.quasiIso C (.up ℤ)).hasLocalizationOfLocallySmall
    (HomologicalComplex.quasiIso C (.up ℤ)).Q

end CategoryTheory.IsGrothendieckAbelian
