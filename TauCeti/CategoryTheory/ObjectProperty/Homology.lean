/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Object properties of homology and left derived functors

A property closed under subobjects and quotients, for instance a Serre class, passes from the
middle object of a short complex to its homology, and so from the degree-`i` term of a complex to
its degree-`i` homology. If an additive functor sends projective objects to objects with this
property, all its left derived functors take values in the same class. Applied to tensoring with
a fixed object, this turns closure of such a class under tensor products into closure under Tor.

## Main results

* `CategoryTheory.ObjectProperty.prop_homology_of_prop_X₂`: the homology of a short complex lies
  in the class if its middle object does.
* `CategoryTheory.ObjectProperty.prop_homology`: the same for the homology of a complex.
* `CategoryTheory.ObjectProperty.prop_leftDerived_obj`: left derived functors take values in the
  class if the functor does on projective objects.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 2.4.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- The homology of a short complex lies in a class of objects closed under subobjects and
quotients, for instance a Serre class, if its middle object does: it is a quotient of the cycles,
which are a subobject of the middle object. -/
lemma prop_homology_of_prop_X₂ {S : ShortComplex C} [S.HasHomology] (h : P S.X₂) :
    P S.homology :=
  P.prop_of_epi S.homologyπ (P.prop_of_mono S.iCycles h)

/-- A property closed under subobjects and quotients passes from a term of a complex to homology
in the same degree, whenever that homology exists. -/
lemma prop_homology {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i : ι) [K.HasHomology i] (h : P (K.X i)) :
    P (K.homology i) :=
  -- `K.homology i` is by definition the homology of the short complex `K.sc i`, whose middle
  -- object is `K.X i`.
  P.prop_homology_of_prop_X₂ (S := K.sc i) h

end HasZeroMorphisms

variable [Abelian C]

/-- If an additive functor sends every projective object into a class closed under subobjects
and quotients, all its left derived functors take values in that class. -/
lemma prop_leftDerived_obj
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasProjectiveResolutions D]
    (F : D ⥤ C) [F.Additive] (hF : ∀ (Y : D) [Projective Y], P (F.obj Y))
    (X : D) (n : ℕ) : P ((F.leftDerived n).obj X) := by
  let Q := projectiveResolution X
  exact P.prop_of_iso (Q.isoLeftDerivedObj F n).symm
    (P.prop_homology ((F.mapHomologicalComplex _).obj Q.complex) n (hF _))

end CategoryTheory.ObjectProperty
