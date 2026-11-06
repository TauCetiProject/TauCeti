/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Named sheafification and `Ext` instances for sheaves on a space

Sheaves of abelian groups, and sheaves of modules over a ring, on a topological space `X` admit
sheafification and have small `Ext` groups. Mathlib finds both facts by instance search, but the
`HasExt` proof found that way records in its type the instance terms of the particular search, and
the kernel unfolds the derived category to compare two such types. This file states the facts once
as named instances, so that every declaration about the cohomology of sheaves on a space elaborates
them to the same constants and the kernel compares them syntactically.

## Main declarations

* `TopCat.hasSheafify_addCommGrpCat`, `TopCat.Sheaf.hasExt_addCommGrpCat`: sheafification and small
  `Ext` groups for sheaves of abelian groups.
* `TopCat.hasSheafify_moduleCat`, `TopCat.Sheaf.hasExt_moduleCat`: the same for sheaves of
  `R`-modules.
-/

public section

open CategoryTheory TopologicalSpace

universe u

/-- Sheafification of presheaves of abelian groups on a space, as a single named instance, so that
every declaration elaborates it to the same term. -/
instance TopCat.hasSheafify_addCommGrpCat (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  inferInstance

/-- Sheaves of abelian groups on a space have small `Ext` groups. Elaborating this instance through
one named constant keeps its type syntactically the same in every declaration: an instance found
through `CategoryTheory.IsGrothendieckAbelian.hasExt` records the instance terms it was found with
in its type, and the kernel then unfolds the derived category to compare two such types. -/
instance TopCat.Sheaf.hasExt_addCommGrpCat (X : TopCat.{u}) :
    HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  inferInstance

/-- Sheafification of presheaves of `R`-modules on a space, as a single named instance, so that
every declaration elaborates it to the same term. -/
instance TopCat.hasSheafify_moduleCat (R : Type u) [Ring R] (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  inferInstance

/-- Sheaves of `R`-modules on a space have small `Ext` groups, as a single named instance, for the
reason given at `TopCat.Sheaf.hasExt_addCommGrpCat`. -/
instance TopCat.Sheaf.hasExt_moduleCat (R : Type u) [Ring R] (X : TopCat.{u}) :
    HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :=
  inferInstance
