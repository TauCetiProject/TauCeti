/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Sites.Descent.GerbeLocalCovers

/-!
# Checks for the local covers of a pseudofunctor

On the point site `Discrete PUnit`, the constant pseudofunctor with fibre a category `D` (built
with Mathlib's `Functor.toPseudofunctor'`) has object cover the empty sieve when `D` is empty and
the maximal sieve when `D` is nonempty. For the discrete fibre `Discrete Bool` the isomorphism
cover of `false` and `true` is empty, since a nonempty fibre need not be locally connected, while
the isomorphism cover of `false` with itself is maximal. No gerbe or covering hypothesis is
asserted for these fixtures.
-/

public section

namespace TauCeti.Examples.GerbeLocalCovers

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.GerbeLocalCovers
  Opposite Bicategory

/-- The constant pseudofunctor on the point site with fibre `D`. -/
abbrev constPoint (D : Type) [Category.{0} D] :
    LocallyDiscrete (Discrete PUnit.{1})ᵒᵖ ⥤ᵖ Cat.{0, 0} :=
  ((Functor.const (Discrete PUnit.{1})ᵒᵖ).obj (Cat.of D)).toPseudofunctor'

/-- The point of the site. -/
abbrev pt : Discrete PUnit.{1} := ⟨⟨⟩⟩

/-- The object `b` of the fibre `Discrete Bool` over the point. -/
abbrev boolObj (b : Bool) : (constPoint (Discrete Bool)).obj (.mk (op pt)) :=
  (⟨b⟩ : Discrete Bool)

/-- **Empty fibre.** For the constant fibre `Discrete PEmpty`, the object cover is the empty
sieve. -/
example : objectCover (constPoint (Discrete PEmpty.{1})) pt = ⊥ :=
  objectCover_eq_bot_iff.2 fun _ _ ↦ ⟨fun x ↦ (x : Discrete PEmpty).as.elim⟩

/-- **Nonempty fibre.** For the constant fibre `Discrete Bool`, the object cover is the maximal
sieve, witnessed by the local object `false`. -/
example : objectCover (constPoint (Discrete Bool)) pt = ⊤ :=
  objectCover_eq_top_iff.2 ⟨boolObj false⟩

/-- **Not locally connected.** For the constant fibre `Discrete Bool`, the isomorphism cover of
`false` and `true` is the empty sieve. -/
example : isomCover (constPoint (Discrete Bool)) (boolObj false) (boolObj true) = ⊥ :=
  eq_bot_iff.2 fun _ f hf ↦ by
    obtain ⟨e⟩ := (mem_isomCover_iff _ _ f).1 hf
    -- The constant pseudofunctor maps every arrow to the identity functor of the fibre.
    simp only [Functor.toPseudofunctor'_map, Quiver.Hom.toLoc, Functor.const_obj_map,
      Cat.Hom.id_toFunctor, Functor.id_obj] at e
    exact Bool.false_ne_true (Discrete.eq_of_hom e.hom)

/-- For the constant fibre `Discrete Bool`, the isomorphism cover of `false` with itself is the
maximal sieve. -/
example : isomCover (constPoint (Discrete Bool)) (boolObj false) (boolObj false) = ⊤ :=
  isomCover_self _

end TauCeti.Examples.GerbeLocalCovers
