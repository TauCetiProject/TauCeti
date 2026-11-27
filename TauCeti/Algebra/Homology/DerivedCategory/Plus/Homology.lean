/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Homology of the bounded below derived category

The homology functor on the bounded below derived category computes the same homology
as that of the bounded below homotopy category before localization.
-/

public section

open CategoryTheory

namespace DerivedCategory.Plus

/-- The homology of a localized bounded below complex is its homotopy-category homology. -/
noncomputable def homologyFunctorFactorsh (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) :
    Qh ⋙ homologyFunctor C n ≅ HomotopyCategory.Plus.ι C ⋙
      HomotopyCategory.homologyFunctor C (.up ℤ) n :=
  (Functor.associator Qh ι (DerivedCategory.homologyFunctor C n)).symm ≪≫
    Functor.isoWhiskerRight (QhCompιIsoιCompQh C) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactorsh C n)

end DerivedCategory.Plus
