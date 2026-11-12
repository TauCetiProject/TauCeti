/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adhesive.PushoutProduct
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Pullback-homs and lifting against monomorphisms

In an adhesive cartesian closed category, the pullback-hom of a monomorphism
and a map lifting against all monomorphisms again lifts against all
monomorphisms. This supplies the trivial-fibration case of the mapping-space
corner axiom, for example in simplicial sets.

The result combines Mathlib's parametrized lifting adjunction with Jack
McKoen's theorem that pushout-products of monomorphisms in adhesive cartesian
monoidal categories are monomorphisms. It uses the native
`Functor.PullbackObjObj` and assumes no model structure.
-/

public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed Limits MorphismProperty

namespace CategoryTheory.Functor.PullbackObjObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [Adhesive C] [HasPushouts C]
  {A X E B : C} {i : A ⟶ X} {p : E ⟶ B}

/-- A pullback-hom corner lifts against all monomorphisms if its source map is
monomorphic and its target map lifts against all monomorphisms. -/
lemma rlp_monomorphisms (P : internalHom.PullbackObjObj i p) [Mono i]
    (hp : (monomorphisms C).rlp p) : (monomorphisms C).rlp P.π := by
  intro K L j (_ : Mono j)
  let Q := Functor.PushoutObjObj.ofHasPushout (curriedTensor C) i j
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff Q]
  have : Mono (CategoryTheory.Arrow.mk i).hom := inferInstanceAs (Mono i)
  have : Mono (CategoryTheory.Arrow.mk j).hom := inferInstanceAs (Mono j)
  -- Q uses the same chosen pushout as the native arrow pushout-product.
  exact hp Q.ι (inferInstanceAs
    (Mono ((CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom)))

end CategoryTheory.Functor.PullbackObjObj
