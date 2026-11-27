/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Homology.DerivedCategory.Grothendieck
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Universes of derived morphisms for modules and sheaves

These examples check that the small-Hom derived category has actual morphism types in
`Type u`, for modules, module sheaves on a small ringed site, and étale module sheaves on a
scheme in universe `u`. The last category has larger morphism types before deriving, so
the bound is stronger than simply retaining the original morphism universe.

The Ext comparison uses Mathlib's existing equivalence with derived morphisms. A separate
example retains the standard larger derived category and checks that its morphism types
are still small in the smaller universe; no particular localization choice is required
for local smallness.
-/

noncomputable section

open CategoryTheory

universe w v u

namespace TauCeti

example (R : Type u) [Ring R] (K L : DerivedCategory (ModuleCat.{u} R)) : Type u :=
  K ⟶ L

example {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (K L : DerivedCategory (SheafOfModules.{u} R)) : Type u :=
  K ⟶ L

example (X : AlgebraicGeometry.Scheme.{u}) (R : Type u) [Ring R]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) : Type u :=
  K ⟶ L

example (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (X Y : C) (n : ℕ) :
    Abelian.Ext.{w} X Y n ≃
      ((DerivedCategory.singleFunctor C 0).obj X ⟶
        ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :=
  Abelian.Ext.homEquiv

example (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    letI := HasDerivedCategory.standard C
    LocallySmall.{w} (DerivedCategory C) := by
  let := HasDerivedCategory.standard C
  exact DerivedCategory.locallySmall_of_hasKInjectiveResolutions

end TauCeti
