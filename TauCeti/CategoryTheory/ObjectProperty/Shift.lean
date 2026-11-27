/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Essential images stable under shifts

The essential image of a functor commuting with shifts is stable under shifts
(`CategoryTheory.Functor.essImage_isStableUnderShift`). No fullness is needed, unlike for the
triangulated subcategory structure on the essential image of a full triangle functor.

## Main results

* `CategoryTheory.Functor.essImage_isStableUnderShift`: the essential image of a functor
  commuting with shifts is stable under shifts.
-/

public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {A : Type*} [AddMonoid A] [HasShift C A]
  [HasShift D A]

/-- The essential image of a functor commuting with shifts is stable under shifts: if
`F.obj X ≅ Y`, then `F.obj (X⟦a⟧) ≅ (F.obj X)⟦a⟧ ≅ Y⟦a⟧`. -/
instance essImage_isStableUnderShift (F : C ⥤ D) [F.CommShift A] :
    F.essImage.IsStableUnderShift A where
  isStableUnderShiftBy a := ⟨by
    rintro Y ⟨X, ⟨e⟩⟩
    exact ⟨X⟦a⟧, ⟨(F.commShiftIso a).app X ≪≫ (shiftFunctor D a).mapIso e⟩⟩⟩

end CategoryTheory.Functor
