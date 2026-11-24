/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import TauCeti.CategoryTheory.ObjectProperty.ArrowIso

/-!
# Monomorphisms whose cokernel satisfies a property

Given a property `S` of objects of a category with cokernels, `S.monoWithCokernel` is the property
of morphisms which are monomorphisms whose cokernel satisfies `S`. Such classes of morphisms are
the building blocks of transfinite compositions in small object arguments, for instance when
writing a monomorphic quasi-isomorphism of complexes as a transfinite composition of
monomorphisms with small acyclic cokernels.

## Main definitions

* `CategoryTheory.ObjectProperty.monoWithCokernel`: the monomorphisms whose cokernel satisfies `S`.
  It respects isomorphisms of arrows when `S` is closed under isomorphisms, because the cokernel
  of a morphism satisfies such a property as soon as that of an isomorphic arrow does
  (`CategoryTheory.ObjectProperty.prop_cokernel_of_arrowIso`).
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

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
