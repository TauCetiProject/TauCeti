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
`Pi.eval C i : (∀ j, C j) ⥤ C i` with the composite of equivalences and `Prod.fst`.
Consequently, each `Pi.eval C i` preserves epimorphisms and limits of arbitrary size without
universe restrictions on the index type or diagram category (complementing
`Mathlib.CategoryTheory.Limits.Pi`), the evaluation functors are jointly faithful
(`CategoryTheory.Pi.jointlyFaithful_eval`), and epimorphisms in `∀ i, C i` are characterized
componentwise (`CategoryTheory.Pi.epi_iff`).
-/

public section

universe w v v' u u'

namespace CategoryTheory

open Limits

namespace Pi

variable {I : Type w} {C : I → Type u} [∀ i, Category.{v} (C i)]

variable (C) in
/-- The evaluation functors out of an indexed product of categories are jointly faithful. -/
theorem jointlyFaithful_eval : JointlyFaithful (Pi.eval C) :=
  ⟨fun h ↦ funext h⟩

/-- Splitting off coordinate `i` identifies `Pi.eval C i` with a composite of equivalences and
`Prod.fst`. -/
private noncomputable def evalIso (i : I) :
    letI := Classical.decEq I
    ((Pi.equivalenceOfEquiv C (Equiv.optionSubtypeNe i)).inverse ⋙
        (Pi.optionEquivalence _).functor ⋙ Prod.fst _ _) ⋙
      (Pi.eqToEquivalence C (Equiv.optionSubtypeNe_none i)).functor ≅ Pi.eval C i :=
  letI := Classical.decEq I
  let e := Equiv.optionSubtypeNe i
  let h₁ : (Pi.optionEquivalence (fun k ↦ C (e k))).functor ⋙ Prod.fst _ _ ≅
      Pi.eval (fun k ↦ C (e k)) none :=
    eqToIso (congrArg (· ⋙ Prod.fst _ _) (Pi.optionEquivalence_functor _)) ≪≫
      Functor.prod'CompFst _ _
  let h₂ : (Pi.equivalenceOfEquiv C e).inverse ⋙ Pi.eval (fun k ↦ C (e k)) none ≅
      Pi.eval C (e none) :=
    eqToIso (congrArg (· ⋙ Pi.eval _ none) (Pi.equivalenceOfEquiv_inverse C e)) ≪≫
      Functor.pi'CompEval _ none
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ h₁ ≪≫ h₂) _ ≪≫
    Pi.evalCompEqToEquivalenceFunctor C (Equiv.optionSubtypeNe_none i)

/-- Every evaluation functor `Pi.eval C i : (∀ i, C i) ⥤ C i` preserves epimorphisms. -/
instance preservesEpimorphisms_eval (i : I) : (Pi.eval C i).PreservesEpimorphisms :=
  Functor.PreservesEpimorphisms.of_iso (evalIso i)

/-- A morphism in an indexed product of categories is an epimorphism if and only if each of its
components is an epimorphism. -/
theorem epi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) : Epi f ↔ ∀ i, Epi (f i) :=
  (jointlyFaithful_eval C).jointlyReflectEpimorphisms.epi_iff f

/-- Every evaluation functor `Pi.eval C i : (∀ i, C i) ⥤ C i` preserves limits of any size, with
no assumption that limits exist in the other factors. -/
instance preservesLimitsOfSize_eval (i : I) : PreservesLimitsOfSize.{v', u'} (Pi.eval C i) :=
  preservesLimits_of_natIso (evalIso i)

end Pi

end CategoryTheory
