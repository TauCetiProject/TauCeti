/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Injective

/-!
# Frobenius exact categories

An exact structure has enough projectives when every object is the third term of a conflation
whose middle term is relatively projective. Dually, it has enough injectives when every object is
the first term of a conflation whose middle term is relatively injective. The projective and
injective modules record these conditions using bundled presentations; this file defines a
Frobenius exact structure by requiring both conditions and equality of the two relative object
classes.

The definition is deliberately a property of a specified `TauCeti.ExactStructure`: an additive
category can carry more than one exact structure, with different projective and injective objects.
The split exact structure is the basic example, while the abelian comparison lemmas turn Mathlib's
ordinary enough-projective and enough-injective hypotheses into presentations for the canonical
abelian exact structure.

This is the input for the stable-category construction: choosing the presentations supplies the
projective-injective middle terms used to define suspension and loop objects.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>, Sections 11–13.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure

/-- A Frobenius exact structure has enough relative projectives and injectives, and these two
classes of objects coincide. -/
structure IsFrobenius (E : ExactStructure C) : Prop where
  /-- Every object admits a relative projective presentation. -/
  enoughProjectives : E.EnoughProjectives
  /-- Every object admits a relative injective presentation. -/
  enoughInjectives : E.EnoughInjectives
  /-- The relatively projective objects are exactly the relatively injective objects. -/
  projective_iff_injective : ∀ X : C, E.isProjective X ↔ E.isInjective X

namespace IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

/-- In a Frobenius exact structure, relative injectivity is equivalent to relative projectivity. -/
theorem injective_iff_projective (hE : E.IsFrobenius) (X : C) :
    E.isInjective X ↔ E.isProjective X :=
  (IsFrobenius.projective_iff_injective hE X).symm

end IsFrobenius

/-- Every split exact structure is Frobenius: all objects are both relatively projective and
relatively injective. -/
theorem split_isFrobenius : (ExactStructure.split C).IsFrobenius where
  enoughProjectives := split_enoughProjectives
  enoughInjectives := split_enoughInjectives
  projective_iff_injective X := ⟨fun _ ↦ split_isInjective X, fun _ ↦ split_isProjective X⟩

end ExactStructure

end TauCeti
