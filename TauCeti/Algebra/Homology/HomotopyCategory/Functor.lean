/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Functors induced on homotopy categories

For an additive functor `F : V ⥤ W`, Mathlib's `CategoryTheory.Functor.mapHomotopyCategory`
is the functor induced on homotopy categories and
`CategoryTheory.Functor.mapHomotopyCategoryFactors` identifies its composite with the quotient
functor. This file records computation rules for working with them on the images of complexes.

For additive functors `F₁ : V ⥤ W`, `G₁ : W ⥤ W'` and `H₁ : V ⥤ W'` with `e : F₁ ⋙ G₁ ≅ H₁`,
Mathlib's `CategoryTheory.Functor.mapHomotopyCategoryCompIso` identifies the induced functors on
homotopy categories; it is induced from `CategoryTheory.Functor.mapHomologicalComplexCompIso`,
and the file also records its components on the class of a complex.

## Main results

* `CategoryTheory.Functor.mapHomotopyCategory_obj_quotient_obj`: the induced functor sends the
  image of a complex `K` to the image of `F` applied to `K`, a definitional equality usable with
  `dsimp` to match objects that Mathlib's `CategoryTheory.Functor.mapHomotopyCategory_obj`
  presents as structures.
* `CategoryTheory.Functor.mapHomotopyCategoryFactors_inv_app`: the inverse of the identification
  is the identity on every complex, dual to Mathlib's
  `CategoryTheory.Functor.mapHomotopyCategoryFactors_hom_app`.
* `HomotopyCategory.quotient_functor_map`: a morphism of complexes sent to the homotopy category
  by the quotient functor `CategoryTheory.Quotient.functor` of the homotopy relation, the form in
  which it appears in the naturality goals of `CategoryTheory.Quotient.natTransLift`, is its image
  under `HomotopyCategory.quotient`, so that lemmas such as Mathlib's
  `CategoryTheory.Functor.mapHomotopyCategory_map` apply.
* `CategoryTheory.Functor.mapHomotopyCategoryCompIso_hom_app_quotient_obj`,
  `CategoryTheory.Functor.mapHomotopyCategoryCompIso_inv_app_quotient_obj`: on the class of a
  complex, the comparison and its inverse are the classes of the homological-complex comparisons.
-/

public section

open CategoryTheory

namespace HomotopyCategory

variable {ι : Type*} {V : Type*} [Category* V] [Preadditive V] {c : ComplexShape ι}

/-- A morphism of complexes sent to the homotopy category by the quotient functor
`Quotient.functor` of the homotopy relation is its image under `HomotopyCategory.quotient`. -/
lemma quotient_functor_map {K L : HomologicalComplex V c} (f : K ⟶ L) :
    (Quotient.functor (homotopic V c)).map f = (quotient V c).map f :=
  rfl

end HomotopyCategory

namespace CategoryTheory.Functor

variable {ι : Type*} {V W : Type*} [Category* V] [Preadditive V] [Category* W] [Preadditive W]
  (F : V ⥤ W) [F.Additive] {c : ComplexShape ι}

/-- The functor `Functor.mapHomotopyCategory` sends the image of a complex `K` in the homotopy
category to the image of `F` applied to `K`. -/
lemma mapHomotopyCategory_obj_quotient_obj (K : HomologicalComplex V c) :
    (F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W c).obj ((F.mapHomologicalComplex c).obj K) :=
  rfl

/-- The inverse of `Functor.mapHomotopyCategoryFactors` is the identity on every complex. -/
lemma mapHomotopyCategoryFactors_inv_app (K : HomologicalComplex V c) :
    (F.mapHomotopyCategoryFactors c).inv.app K =
      𝟙 ((HomotopyCategory.quotient W c).obj ((F.mapHomologicalComplex c).obj K)) :=
  rfl

end CategoryTheory.Functor

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
