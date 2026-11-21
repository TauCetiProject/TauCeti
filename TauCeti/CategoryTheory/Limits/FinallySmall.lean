/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FinallySmall

/-!
# Initial smallness of categories of elements

This file records that initial smallness of the category of elements `G.Elements` of a functor
`G : C ⥤ Type w'` is invariant under natural isomorphism (`initiallySmall_elements_of_iso`).
-/

public section

universe w w'

namespace CategoryTheory

/-- If `G₁ ≅ G₂` is a natural isomorphism of functors to types, then `G₁.Elements` inherits
`InitiallySmall` from `G₂.Elements`. -/
lemma initiallySmall_elements_of_iso {C : Type*} [Category* C] {G₁ G₂ : C ⥤ Type w'}
    (e : G₁ ≅ G₂) [InitiallySmall.{w} G₂.Elements] :
    InitiallySmall.{w} G₁.Elements :=
  let eqv : G₁.Elements ≌ G₂.Elements := Cat.equivOfIso (Functor.elementsFunctor.mapIso e)
  initiallySmall_of_initial_of_initiallySmall eqv.inverse

end CategoryTheory
