/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Projective objects: isomorphism closure and coproducts

The object property `CategoryTheory.isProjective C` of being projective is closed under
isomorphisms, so it can serve as the resolving property of finite resolutions, which are
transported along isomorphisms.

The point of any colimit cofan of a family of projective objects is projective. Mathlib's
instance for the chosen coproduct `∐ X` requires the index type to live in the universe of the
morphisms of the category; the version here accepts any colimit cofan with any index type, for
instance a coproduct of a sequence of modules indexed by `ℕ` in `ModuleCat.{v} R`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C]

/-- Being projective is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms_isProjective : (isProjective C).IsClosedUnderIsomorphisms :=
  ⟨fun e h => @Projective.of_iso _ _ _ _ e h⟩

namespace Projective

/-- The point of a colimit cofan of projective objects is projective. -/
theorem of_isColimit_cofan {ι : Type*} {X : ι → C} [∀ i, Projective (X i)] {c : Cofan X}
    (hc : IsColimit c) : Projective c.pt where
  factors f e _ := ⟨Cofan.IsColimit.desc hc fun i ↦ factorThru (c.inj i ≫ f) e,
    Cofan.IsColimit.hom_ext hc _ _ fun i ↦ by simp⟩

end Projective

end CategoryTheory
