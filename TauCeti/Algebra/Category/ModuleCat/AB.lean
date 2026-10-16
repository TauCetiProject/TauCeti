/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Exact products of modules with independent universes

Products of modules are exact even when the coefficient ring and the modules live in different
universes. This supplies the exactness needed to commute cohomology with products of cochain
complexes. The index type must be small in the universe of the modules.

The argument is Mathlib's `AB4Star` instance for `ModuleCat`, by Dagur Asgeirsson: transfer
exactness from abelian groups along the forgetful functor. Here the index type is first replaced
by a small copy, and the ring universe is independent of the module universe.
-/

public section

open CategoryTheory Limits

universe w v u

namespace TauCeti

/-- Products of modules indexed by a small type are exact, with no restriction on the universe
of the coefficient ring. -/
instance moduleCat_hasExactLimitsOfShape_discrete (R : Type u) [Ring R]
    (ι : Type w) [Small.{v} ι] [HasLimitsOfShape (Discrete ι) (ModuleCat.{v} R)] :
    HasExactLimitsOfShape (Discrete ι) (ModuleCat.{v} R) := by
  have : HasExactLimitsOfShape (Discrete ι) AddCommGrpCat.{v} :=
    HasExactLimitsOfShape.of_domain_equivalence _ (Discrete.equivalence (equivShrink.{v} ι)).symm
  have : PreservesLimitsOfShape (Discrete ι) (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
    preservesLimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{v} ι)).symm _
  have : PreservesFiniteColimits (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : ReflectsFiniteColimits (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
    { reflects := fun _ _ _ ↦ inferInstance }
  exact HasExactLimitsOfShape.domain_of_functor (C := ModuleCat.{v} R)
    (D := AddCommGrpCat.{v}) (Discrete ι) (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})

end TauCeti
