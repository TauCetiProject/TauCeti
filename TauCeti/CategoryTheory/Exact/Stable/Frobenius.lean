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
the first term of a conflation whose middle term is relatively injective. This file records these
conditions using bundled presentations, and defines a Frobenius exact structure by requiring both
conditions and equality of the two relative object classes.

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

/-- A projective presentation of `X` relative to `E` is a conflation `K → P → X` whose
middle term is `E`-projective. -/
structure ProjectivePresentation (E : ExactStructure C) (X : C) where
  /-- The kernel term of the presentation. -/
  K : C
  /-- The relatively projective middle term. -/
  P : C
  /-- The inflation into the projective term. -/
  i : K ⟶ P
  /-- The deflation onto the presented object. -/
  p : P ⟶ X
  /-- The two presentation maps form a short complex. -/
  zero : i ≫ p = 0
  /-- The presentation is a conflation of `E`. -/
  conflation : E.Conflation (ShortComplex.mk i p zero)
  /-- The middle term is projective relative to `E`. -/
  isProjective : E.isProjective P

/-- An injective presentation of `X` relative to `E` is a conflation `X → I → K` whose
middle term is `E`-injective. -/
structure InjectivePresentation (E : ExactStructure C) (X : C) where
  /-- The relatively injective middle term. -/
  I : C
  /-- The cokernel term of the presentation. -/
  K : C
  /-- The inflation from the presented object. -/
  i : X ⟶ I
  /-- The deflation from the injective term. -/
  p : I ⟶ K
  /-- The two presentation maps form a short complex. -/
  zero : i ≫ p = 0
  /-- The presentation is a conflation of `E`. -/
  conflation : E.Conflation (ShortComplex.mk i p zero)
  /-- The middle term is injective relative to `E`. -/
  isInjective : E.isInjective I

/-- An exact structure has enough projectives if every object admits a relative projective
presentation. -/
structure EnoughProjectives (E : ExactStructure C) : Prop where
  presentation : ∀ X : C, Nonempty (E.ProjectivePresentation X)

/-- An exact structure has enough injectives if every object admits a relative injective
presentation. -/
structure EnoughInjectives (E : ExactStructure C) : Prop where
  presentation : ∀ X : C, Nonempty (E.InjectivePresentation X)

namespace ProjectivePresentation

/-- The tautological projective presentation in the split exact structure. -/
noncomputable def split (X : C) : (ExactStructure.split C).ProjectivePresentation X where
  K := 0
  P := X
  i := 0
  p := 𝟙 X
  zero := by simp
  conflation := (ExactStructure.split C).conflation_zero_id X
  isProjective := split_isProjective X

/-- Mathlib's projective presentation gives a relative projective presentation for the canonical
exact structure of an abelian category. -/
noncomputable def abelian {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughProjectives A] (X : A) :
    (ExactStructure.abelian A).ProjectivePresentation X where
  K := kernel (Projective.π X)
  P := Projective.over X
  i := kernel.ι (Projective.π X)
  p := Projective.π X
  zero := kernel.condition _
  conflation := abelian_conflation_of_epi _
  isProjective := (abelian_isProjective_iff _).mpr inferInstance

end ProjectivePresentation

namespace InjectivePresentation

/-- The tautological injective presentation in the split exact structure. -/
noncomputable def split (X : C) : (ExactStructure.split C).InjectivePresentation X where
  I := X
  K := 0
  i := 𝟙 X
  p := 0
  zero := by simp
  conflation := (ExactStructure.split C).conflation_id_zero X
  isInjective := split_isInjective X

/-- Mathlib's injective presentation gives a relative injective presentation for the canonical
exact structure of an abelian category. -/
noncomputable def abelian {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughInjectives A] (X : A) :
    (ExactStructure.abelian A).InjectivePresentation X where
  I := Injective.under X
  K := cokernel (Injective.ι X)
  i := Injective.ι X
  p := cokernel.π (Injective.ι X)
  zero := cokernel.condition _
  conflation := abelian_conflation_of_mono _
  isInjective := (abelian_isInjective_iff _).mpr inferInstance

end InjectivePresentation

/-- The split exact structure has enough relative projectives. -/
theorem split_enoughProjectives : (ExactStructure.split C).EnoughProjectives :=
  ⟨fun X ↦ ⟨ProjectivePresentation.split X⟩⟩

/-- The split exact structure has enough relative injectives. -/
theorem split_enoughInjectives : (ExactStructure.split C).EnoughInjectives :=
  ⟨fun X ↦ ⟨InjectivePresentation.split X⟩⟩

/-- Enough ordinary projectives give enough relative projectives for the canonical exact
structure on an abelian category. -/
theorem abelian_enoughProjectives {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughProjectives A] : (ExactStructure.abelian A).EnoughProjectives :=
  ⟨fun X ↦ ⟨ProjectivePresentation.abelian X⟩⟩

/-- Enough ordinary injectives give enough relative injectives for the canonical exact structure
on an abelian category. -/
theorem abelian_enoughInjectives {A : Type u} [Category.{v} A] [Abelian A]
    [CategoryTheory.EnoughInjectives A] : (ExactStructure.abelian A).EnoughInjectives :=
  ⟨fun X ↦ ⟨InjectivePresentation.abelian X⟩⟩

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

/-- Choose a relative projective presentation in a Frobenius exact structure. -/
noncomputable def projectivePresentation (X : C) : E.ProjectivePresentation X :=
  (hE.enoughProjectives.presentation X).some

/-- Choose a relative injective presentation in a Frobenius exact structure. -/
noncomputable def injectivePresentation (X : C) : E.InjectivePresentation X :=
  (hE.enoughInjectives.presentation X).some

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
