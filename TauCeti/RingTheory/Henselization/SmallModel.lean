/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import TauCeti.RingTheory.Henselization.Neighbourhood

/-!
# A small model for étale neighbourhoods

The category of étale neighbourhoods of a ring and ideal is essentially small. This permits
forming its filtered colimit in the category of algebras when constructing the henselization of
the pair.

The small model is not built here: it comes from Mathlib's category `FGAlgCat` of finite-type
algebras and its essential-smallness instance in `Mathlib.Algebra.Category.CommAlgCat.FiniteType`.
Étale algebras are finitely presented, hence of finite type, so the neighbourhoods embed fully
faithfully into `FGAlgCat`, and essential smallness transfers along this embedding.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

/-- The category of étale neighbourhoods of `(R, I)` is essentially small. -/
theorem neighbourhood_essentiallySmall (I : Ideal R) :
    EssentiallySmall.{u} (Neighbourhood.{u, v} I) := by
  apply essentiallySmall_of_fully_faithful
    (ObjectProperty.ιOfLE (P := IsNeighbourhood I)
      (P' := fun A : CommAlgCat.{v} R ↦ Algebra.FiniteType R A) fun A hA ↦ ?_)
  exact @Algebra.FiniteType.of_finitePresentation R A _ _ _
    ((isNeighbourhood_iff I A).mp hA).1.finitePresentation

attribute [instance] neighbourhood_essentiallySmall

end TauCeti.Henselization
