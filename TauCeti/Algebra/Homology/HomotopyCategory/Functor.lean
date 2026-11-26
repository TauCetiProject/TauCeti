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
