/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-!
# Forgetting the module structure of a sheaf of modules is exact

Let `R` be a sheaf of rings on a site `(C, J)`. Mathlib's `SheafOfModules.toSheaf R` sends a
sheaf of `R`-modules to its underlying abelian sheaf, and knows that this functor preserves and
reflects finite limits. This file supplies the missing half: it preserves every shape of colimits
that abelian groups have, in particular finite colimits, hence carries short exact sequences of
sheaves of modules to short exact sequences of abelian sheaves.

## Main declarations

* `TauCeti.SheafOfModules.preservesColimitsOfShape_toSheaf`: `SheafOfModules.toSheaf`
  preserves colimits of any shape that exists in `AddCommGrpCat`;
* `TauCeti.SheafOfModules.preservesFiniteColimits_toSheaf`: `SheafOfModules.toSheaf` preserves
  finite colimits;
* `TauCeti.SheafOfModules.shortExact_map_toSheaf`: a short exact sequence of sheaves of modules
  stays short exact after forgetting the module structures.

## Implementation notes

The sheafification of presheaves of modules is left adjoint to a fully faithful functor, and
composing it with `SheafOfModules.toSheaf` gives `PresheafOfModules.toPresheaf ⋙ presheafToSheaf`,
which preserves colimits because colimits of presheaves of modules are computed sectionwise and
`presheafToSheaf` is a left adjoint. `Adjunction.preservesColimitsOfShape_iff` transfers this
to `SheafOfModules.toSheaf`.

Exactness of `SheafOfModules.toSheaf` is what makes the cohomology of a sheaf of modules, which
is defined through the underlying abelian sheaf, fit into a long exact sequence.
-/

public section

open CategoryTheory Limits

universe w w' v v' u u'

noncomputable section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace TauCeti

namespace SheafOfModules

open _root_.SheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{v}]

/-- Forgetting the module structures of sheaves of modules preserves colimits of every shape
along which abelian groups have colimits. -/
instance preservesColimitsOfShape_toSheaf (D : Type w) [Category.{w'} D]
    [HasColimitsOfShape D AddCommGrpCat.{v}] :
    PreservesColimitsOfShape D (toSheaf.{v} R) :=
  ((PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).preservesColimitsOfShape_iff
    _ D).2 <| preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf.{v} (𝟙 R.obj)).symm

/-- Forgetting the module structures of sheaves of modules preserves finite colimits. -/
instance preservesFiniteColimits_toSheaf : PreservesFiniteColimits (toSheaf.{v} R) where
  preservesFiniteColimits _ := inferInstance

end

/-- Forgetting the module structures of a short exact sequence of sheaves of modules leaves a
short exact sequence of abelian sheaves. -/
theorem shortExact_map_toSheaf [HasSheafify J AddCommGrpCat.{v}]
    {S : ShortComplex (_root_.SheafOfModules.{v} R)} (hS : S.ShortExact) :
    (S.map (toSheaf.{v} R)).ShortExact :=
  hS.map_of_exact _

end SheafOfModules

end TauCeti

end
