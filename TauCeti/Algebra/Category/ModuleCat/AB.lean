/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Exact filtered colimits, products and coproducts of modules with independent universes

Filtered colimits, products and coproducts of modules are exact even when the coefficient ring
and the modules live in different universes. This supplies the exactness needed for homology with
varying coefficients and to commute cohomology with products of cochain complexes. The indexing
category or type must be small in the universe of the modules.

The arguments follow Mathlib's AB instances for `ModuleCat`, by Dagur Asgeirsson: transfer
exactness from abelian groups along the forgetful functor. For products, the index type is first
replaced by a small copy. In both cases the ring universe is independent of the module universe.
-/

public section

open CategoryTheory Limits

universe w w' v u

namespace TauCeti

/-- Filtered colimits of modules indexed by small categories are exact, with no restriction on
the universe of the coefficient ring. -/
instance moduleCat_ab5OfSize (R : Type u) [Ring R] [UnivLE.{w, v}] [UnivLE.{w', v}] :
    AB5OfSize.{w, w'} (ModuleCat.{v} R) where
  ofShape J _ _ := by
    have : AB5OfSize.{w, w'} AddCommGrpCat.{v} :=
      AB5OfSize_of_univLE.{w, w', v, v, v, v + 1} _
    exact HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})

/-- Coproducts of modules are exact, with no restriction on the universe of the coefficient
ring. -/
instance moduleCat_ab4OfSize (R : Type u) [Ring R] : AB4OfSize.{v} (ModuleCat.{v} R) := by
  have : HasFiniteBiproducts (ModuleCat.{v} R) := Abelian.hasFiniteBiproducts
  exact AB4.of_AB5 _

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
