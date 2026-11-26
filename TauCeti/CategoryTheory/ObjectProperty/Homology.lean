/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# Object properties of homology

A property closed under subobjects and quotients, for instance a Serre class, passes from the
middle object of a short complex to its homology, and so from the degree-`i` term of a complex to
its degree-`i` homology. The consequence for left derived functors,
`CategoryTheory.ObjectProperty.prop_leftDerived_obj`, is in
`TauCeti.CategoryTheory.Abelian.LeftDerived`.

More generally, a nonempty property closed under kernels and cokernels — for instance a weak Serre
class — passes to the homology of a short complex whenever all three objects of the short complex
lie in the class, since the homology is isomorphic to `cokernel (kernel.lift S.g S.f S.zero)`.

## Main results

* `CategoryTheory.ObjectProperty.prop_homology_of_prop_X₂`: the homology of a short complex lies
  in a class closed under subobjects and quotients if its middle object does.
* `CategoryTheory.ObjectProperty.prop_homology`: the same for the homology of a complex.
* `CategoryTheory.ObjectProperty.prop_shortComplex_homology_of_isClosedUnderKernels`: the homology
  of a short complex lies in a nonempty class closed under kernels and cokernels if all three
  terms of the short complex do.
* `CategoryTheory.ObjectProperty.prop_homology_of_isClosedUnderKernels`: the same for the homology
  of a homological complex.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

universe u v

section SubobjectsQuotients

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

end SubobjectsQuotients

section KernelsCokernels

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)
  [P.Nonempty] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]

/-- The homology of a short complex lies in a nonempty class of objects closed under kernels and
cokernels, such as a weak Serre class, whenever all three terms of the short complex do: the
homology identifies with `cokernel (kernel.lift S.g S.f S.zero)`. -/
lemma prop_shortComplex_homology_of_isClosedUnderKernels {S : ShortComplex C} [S.HasHomology]
    [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)]
    (h₁ : P S.X₁) (h₂ : P S.X₂) (h₃ : P S.X₃) : P S.homology :=
  P.prop_of_iso S.homologyIsoCokernelLift.symm
    (P.prop_cokernel (kernel.lift S.g S.f S.zero) h₁ (P.prop_kernel S.g h₂ h₃))

/-- A nonempty property closed under kernels and cokernels passes to the degree-`i` homology of a
homological complex whenever the terms at `c.prev i`, `i`, and `c.next i` lie in the class. -/
lemma prop_homology_of_isClosedUnderKernels {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i : ι) [K.HasHomology i]
    [HasKernel (K.sc i).g] [HasCokernel (kernel.lift (K.sc i).g (K.sc i).f (K.sc i).zero)]
    (h₁ : P (K.X (c.prev i))) (h₂ : P (K.X i)) (h₃ : P (K.X (c.next i))) :
    P (K.homology i) :=
  P.prop_shortComplex_homology_of_isClosedUnderKernels (S := K.sc i) h₁ h₂ h₃

end KernelsCokernels

end CategoryTheory.ObjectProperty
