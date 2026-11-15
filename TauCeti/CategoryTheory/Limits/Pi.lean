/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Logic.Equiv.Option
public import TauCeti.CategoryTheory.Products.Basic

/-!
# Epimorphisms and limit preservation in indexed product categories

Splitting off a coordinate `i : I` via `Equiv.optionSubtypeNe` and
`CategoryTheory.Pi.optionEquivalence` identifies the evaluation functor
`Pi.eval C i : (∀ j, C j) ⥤ C i` with the composite of two equivalences and `Prod.fst`.
Consequently, each `Pi.eval C i` preserves epimorphisms and limits of arbitrary shape without
universe restrictions on the index type or diagram category (complementing
`Mathlib.CategoryTheory.Limits.Pi`), the evaluation functors are jointly faithful
(`CategoryTheory.JointlyFaithful.piEval`), and epimorphisms in `∀ i, C i` are characterized
componentwise (`CategoryTheory.Pi.epi_iff`).
-/

public section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {I : Type w} {C : I → Type u} [∀ i, Category.{v} (C i)]

variable (C) in
/-- The evaluation functors out of an indexed product of categories are jointly faithful. -/
theorem JointlyFaithful.piEval : JointlyFaithful (Pi.eval C) :=
  ⟨fun h ↦ funext h⟩

namespace Pi

/-- Every evaluation functor `Pi.eval C i : (∀ i, C i) ⥤ C i` preserves epimorphisms. -/
instance preservesEpimorphisms_eval (i : I) : (Pi.eval C i).PreservesEpimorphisms := by
  classical
  exact Functor.PreservesEpimorphisms.of_iso (F :=
    (Pi.equivalenceOfEquiv C (Equiv.optionSubtypeNe i)).inverse ⋙
      (Pi.optionEquivalence _).functor ⋙ Prod.fst _ _) (Iso.refl _)

/-- A morphism in an indexed product of categories is an epimorphism if and only if each of its
components is an epimorphism. -/
theorem epi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) : Epi f ↔ ∀ i, Epi (f i) :=
  (JointlyFaithful.piEval C).jointlyReflectEpimorphisms.epi_iff f

/-- Every evaluation functor `Pi.eval C i : (∀ i, C i) ⥤ C i` preserves limits of any shape, with
no assumption that limits exist in the other factors. -/
instance preservesLimitsOfShape_eval (i : I) {J : Type u'} [Category.{v'} J] :
    PreservesLimitsOfShape J (Pi.eval C i) := by
  classical
  exact preservesLimitsOfShape_of_natIso (F :=
    (Pi.equivalenceOfEquiv C (Equiv.optionSubtypeNe i)).inverse ⋙
      (Pi.optionEquivalence _).functor ⋙ Prod.fst _ _) (Iso.refl _)

end Pi

end CategoryTheory
