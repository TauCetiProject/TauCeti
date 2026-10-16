/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Object properties of homology and left derived functors

A property closed under subobjects and quotients passes from the degree-`i` term of a complex
to its degree-`i` homology. If an additive functor sends projective objects to objects with this
property, all its left derived functors take values in the same class. In particular, tensor
closure of a Serre class implies its closure under Tor.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Section 2.4.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
  [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]

/-- A property closed under subobjects and quotients passes from a term of a complex to homology
in the same degree. -/
lemma prop_homology {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι)
    (h : P (K.X i)) : P (K.homology i) :=
  P.prop_of_epi (K.homologyπ i) (P.prop_of_mono (K.iCycles i) h)

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
