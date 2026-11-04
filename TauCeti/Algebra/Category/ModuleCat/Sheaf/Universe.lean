/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import TauCeti.CategoryTheory.Sites.CoefficientEquivalence

/-!
# Large-universe sheaves of modules over a small ring

The universe of sections of a sheaf need not equal the universe of its scalar ring. Replacing
`R` by the isomorphic ring `ULift R` makes Mathlib's native Grothendieck-abelian instance
applicable. The induced coefficient equivalence of sheaf categories then transports that
instance back to sheaves of `R`-modules, without lifting their section carriers.

On any small site, the section universe may be larger than both the site and the scalar ring.
These sheaves have enough injectives and support the construction of right derived functors.
Sheafification exists in the stated universes; scalar restriction commutes with it by
`CategoryTheory.sheafifyComposeIso`. In particular this applies to the open-set site of a
topological space.

The construction uses Mathlib's `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` and the native
Grothendieck-category theorem `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`.
-/

public section

universe u v w

open CategoryTheory

namespace TauCeti

variable (R : Type u) [Ring R] {C : Type v} [SmallCategory C]
  (J : GrothendieckTopology C)

/-- Module sheafification exists when the section universe is at least as large as those of
the site and scalar ring. -/
instance (priority := 100) hasSheafify_moduleCat :
    HasSheafify J (ModuleCat.{max u v w} R) := by
  -- Fix the small-model hom universe before invoking concrete sheafification.
  let : SmallCategory (SmallModel.{max u v w} C) := smallCategorySmallModel.{max u v w} C
  let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v w}
    (ULift.ringEquiv : ULift.{max v w} R ≃+* R)
  let : HasSheafify J (ModuleCat.{max u v w} (ULift.{max v w} R)) :=
    hasSheafifyEssentiallySmallSite.{v, _, v, _, max u v w} J _
  exact e.hasSheafify_right J

/-- Sheaves of large modules over a possibly smaller ring form a Grothendieck abelian category.
In particular Mathlib's native enough-injectives instance applies. The section universe may
be strictly larger than both the site and scalar universes. -/
instance (priority := 100) isGrothendieckAbelian_sheaf_moduleCat :
    IsGrothendieckAbelian.{max u v w} (Sheaf J (ModuleCat.{max u v w} R)) := by
  let : SmallCategory (SmallModel.{max u v w} C) := smallCategorySmallModel.{max u v w} C
  let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v w}
    (ULift.ringEquiv : ULift.{max v w} R ≃+* R)
  let : IsGrothendieckAbelian.{max u v w}
      (Sheaf J (ModuleCat.{max u v w} (ULift.{max v w} R))) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u v w} J _
  exact IsGrothendieckAbelian.of_equivalence (e.sheafCongrRight J).symm

/-- Module sheaves have enough injectives in every section universe at least as large as the
site and scalar universes. Fixing the Grothendieck universe explicitly avoids inference choosing
the smaller site universe. -/
instance (priority := 100) enoughInjectives_sheaf_moduleCat :
    EnoughInjectives (Sheaf J (ModuleCat.{max u v w} R)) := by
  let : IsGrothendieckAbelian.{max u v w} (Sheaf J (ModuleCat.{max u v w} R)) :=
    isGrothendieckAbelian_sheaf_moduleCat R J
  infer_instance

/-- The enough-injectives comparison for Mathlib's topological-sheaf wrapper. -/
instance (priority := 100) enoughInjectives_topCatSheaf_moduleCat (X : TopCat.{v}) :
    EnoughInjectives (TopCat.Sheaf (ModuleCat.{max u v w} R) X) :=
  enoughInjectives_sheaf_moduleCat.{u, v, w} R (Opens.grothendieckTopology X)

end TauCeti
