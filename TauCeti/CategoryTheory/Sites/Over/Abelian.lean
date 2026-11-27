/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Abelian
public import TauCeti.CategoryTheory.Sites.Abelian.LocallySurjective
public import TauCeti.CategoryTheory.Sites.Continuous
public import TauCeti.CategoryTheory.Sites.Over.Extension

/-!
# Restriction of abelian sheaves to a localized site

Restriction of abelian sheaves to `J.over U` preserves finite colimits, since epimorphisms of
abelian sheaves are locally surjective, and preserves injective objects, since its left adjoint is
exact. Its additivity comes from `TauCeti.CategoryTheory.Sites.Continuous`. The description of the
left adjoint as the sheafified coproduct extension
(`TauCeti.CategoryTheory.Over.sheafPullbackIsoPresheafExtension`) and its exactness
(`TauCeti.CategoryTheory.Over.preservesFiniteLimits_sheafPullback`) are in
`TauCeti.CategoryTheory.Sites.Over.Extension`.
-/

public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.GrothendieckTopology

/-- Restriction of abelian sheaves to a localized site preserves finite colimits: it preserves
finite limits and epimorphisms, since epimorphisms are locally surjective. -/
instance preservesFiniteColimits_overPullback {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}] :
    PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U) := by
  have : (J.overPullback AddCommGrpCat.{v} U).PreservesEpimorphisms :=
    ⟨fun φ _ ↦ by
      have := Sheaf.isLocallySurjective_of_epi_addCommGrp φ
      infer_instance⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (J.overPullback AddCommGrpCat.{v} U)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Restriction of abelian sheaves to a localized site preserves injective objects because its
left adjoint, extension to the ambient site, is exact. -/
instance preservesInjectiveObjects_overPullback {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (U : C) [HasSheafify J AddCommGrpCat.{v}] :
    (J.overPullback AddCommGrpCat.{v} U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{v} (J.over U) J)

end CategoryTheory.GrothendieckTopology
