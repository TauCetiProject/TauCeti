/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Monomorphisms whose cokernel satisfies a property

Given a property `S` of objects of a category with cokernels, `S.monoWithCokernel` is the property
of morphisms which are monomorphisms whose cokernel satisfies `S`. Such classes of morphisms are
the building blocks of transfinite compositions in small object arguments, for instance when
writing a monomorphic quasi-isomorphism of complexes as a transfinite composition of
monomorphisms with small acyclic cokernels.

## Main definitions

* `CategoryTheory.ObjectProperty.monoWithCokernel`: the monomorphisms whose cokernel satisfies `S`.
  It respects isomorphisms of arrows when `S` is closed under isomorphisms, because the kernel and
  the cokernel of a morphism satisfy such a property as soon as those of an isomorphic arrow do
  (`CategoryTheory.ObjectProperty.prop_kernel_of_arrowIso`,
  `CategoryTheory.ObjectProperty.prop_cokernel_of_arrowIso`).
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

section ArrowIso

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ObjectProperty C)
  [S.IsClosedUnderIsomorphisms] {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The kernel of a morphism satisfies a property closed under isomorphisms as soon as the kernel
of an isomorphic arrow does. -/
lemma prop_kernel_of_arrowIso [HasKernel f] [HasKernel f'] (e : Arrow.mk f ≅ Arrow.mk f')
    (h : S (kernel f)) : S (kernel f') :=
  S.prop_of_iso (kernel.mapIso f f' (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
    (Arrow.w e.hom).symm) h

/-- The cokernel of a morphism satisfies a property closed under isomorphisms as soon as the
cokernel of an isomorphic arrow does. -/
lemma prop_cokernel_of_arrowIso [HasCokernel f] [HasCokernel f'] (e : Arrow.mk f ≅ Arrow.mk f')
    (h : S (cokernel f)) : S (cokernel f') :=
  S.prop_of_iso (cokernel.mapIso f f' (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
    (Arrow.w e.hom).symm) h

end ArrowIso

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasCokernels C] (S : ObjectProperty C)

/-- The monomorphisms whose cokernel satisfies `S`. -/
def monoWithCokernel : MorphismProperty C :=
  fun _ _ g ↦ Mono g ∧ S (cokernel g)

variable {S} in
@[simp]
lemma mem_monoWithCokernel_iff {X Y : C} (g : X ⟶ Y) :
    S.monoWithCokernel g ↔ Mono g ∧ S (cokernel g) :=
  Iff.rfl

instance [S.IsClosedUnderIsomorphisms] : S.monoWithCokernel.RespectsIso :=
  .of_respects_arrow_iso _ fun _ _ e ⟨hm, hf⟩ ↦
    ⟨(MorphismProperty.monomorphisms C).arrow_iso_iff e |>.1 hm,
      S.prop_cokernel_of_arrowIso e hf⟩

end CategoryTheory.ObjectProperty
