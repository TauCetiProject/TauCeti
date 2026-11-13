/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Object properties of homology

A property closed under subobjects and quotients, for instance a Serre class, passes from the
middle object of a short complex to its homology, and so from the degree-`i` term of a complex to
its degree-`i` homology. The consequence for left derived functors,
`CategoryTheory.ObjectProperty.prop_leftDerived_obj`, is in
`TauCeti.CategoryTheory.Abelian.LeftDerived`.

## Main results

* `CategoryTheory.ObjectProperty.prop_homology_of_prop_X₂`: the homology of a short complex lies
  in the class if its middle object does.
* `CategoryTheory.ObjectProperty.prop_homology`: the same for the homology of a complex.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)
  [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]

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

end CategoryTheory.ObjectProperty
