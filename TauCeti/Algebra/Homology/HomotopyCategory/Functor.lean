/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Composites of functors on the homotopy category

For additive functors `F₁ : V ⥤ W`, `G₁ : W ⥤ W'` and `H₁ : V ⥤ W'` with `e : F₁ ⋙ G₁ ≅ H₁`,
Mathlib's `CategoryTheory.Functor.mapHomotopyCategoryCompIso` identifies the induced functors on
homotopy categories. It is induced from `CategoryTheory.Functor.mapHomologicalComplexCompIso`,
and this file records its components on the class of a complex.

## Main results

* `CategoryTheory.Functor.mapHomotopyCategoryCompIso_hom_app_quotient_obj`,
  `CategoryTheory.Functor.mapHomotopyCategoryCompIso_inv_app_quotient_obj`: on the class of a
  complex, the comparison and its inverse are the classes of the homological-complex comparisons.
-/

public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {ι : Type*} (c : ComplexShape ι)
  {V W W' : Type*} [Category* V] [Category* W] [Category* W'] [Preadditive V]
  [Preadditive W] [Preadditive W'] {F₁ : V ⥤ W} {G₁ : W ⥤ W'} {H₁ : V ⥤ W'} (e : F₁ ⋙ G₁ ≅ H₁)
  [F₁.Additive] [G₁.Additive] [H₁.Additive]

/-- On the class of a complex, `mapHomotopyCategoryCompIso` is the class of the
homological-complex comparison `mapHomologicalComplexCompIso`. -/
@[simp]
lemma mapHomotopyCategoryCompIso_hom_app_quotient_obj (K : HomologicalComplex V c) :
    (mapHomotopyCategoryCompIso e c).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W' c).map ((mapHomologicalComplexCompIso e c).hom.app K) :=
  Quotient.natTransLift_app _ _ _ _ K

/-- On the class of a complex, the inverse of `mapHomotopyCategoryCompIso` is the class of the
inverse of `mapHomologicalComplexCompIso`. -/
@[simp]
lemma mapHomotopyCategoryCompIso_inv_app_quotient_obj (K : HomologicalComplex V c) :
    (mapHomotopyCategoryCompIso e c).inv.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W' c).map ((mapHomologicalComplexCompIso e c).inv.app K) :=
  Quotient.natTransLift_app _ _ _ _ K

end CategoryTheory.Functor
