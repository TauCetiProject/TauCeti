/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Grothendieck abelian sheaf categories on essentially small sites

Mathlib shows that sheaves on a small site with values in a Grothendieck abelian category form a
Grothendieck abelian category, and transports this to an essentially small site `C` under the
assumption that presheaves on the small model of `C` can be sheafified
(`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`). Here the assumption is
instead that presheaves on `C` itself can be sheafified, with no condition on the size of the hom
types of `C`: sheafification transports to the small model, and the conclusion transports back
along the equivalence of sheaf categories.
-/

public section

universe u v u' v' u₂

namespace CategoryTheory.Sheaf

/-- Sheaves on an essentially small site with values in a Grothendieck abelian category form a
Grothendieck abelian category, provided presheaves on the site can be sheafified: sheafification
transports to the small model of the site, where the small case applies, and the result transports
back along the equivalence of sheaf categories. -/
theorem isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify
    {C : Type u₂} [Category.{v} C] [EssentiallySmall.{u} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] [Abelian A] [IsGrothendieckAbelian.{u} A] [HasSheafify J A] :
    IsGrothendieckAbelian.{u} (Sheaf J A) :=
  have : HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A :=
    have : (equivSmallModel C).symm.inverse.IsDenseSubsite J
        ((equivSmallModel C).inverse.inducedTopology J) :=
      inferInstanceAs ((equivSmallModel C).functor.IsDenseSubsite _ _)
    (equivSmallModel C).symm.hasSheafify _ J A
  IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel C).sheafCongr J ((equivSmallModel C).inverse.inducedTopology J) A).symm

end CategoryTheory.Sheaf
