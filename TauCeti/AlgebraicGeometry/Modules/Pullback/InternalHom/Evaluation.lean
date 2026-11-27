/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.CategoryTheory.Monoidal.Closed.Functor

/-!
# Pullback and global sections of internal Homs

For arbitrary module sheaves, the internal-Hom pullback comparison takes the section of a
module map to the section of its pullback. Equivalently, uncurrying a pulled-back section gives
the pulled-back map.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor.OplaxMonoidal

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

universe u

/-- Pulling back a section of an internal Hom and then evaluating is the pullback of its
uncurried map. -/
theorem pullback_map_uncurry' {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (s : 𝟙_ Y.Modules ⟶ (ihom M).obj N) :
    (pullback f).map (uncurry' s) =
      uncurry' ((pullbackObjUnitIso f).inv ≫ (pullback f).map s ≫
        ((pullback f).ihomComparison M).app N) := by
  have hu : (ρ_ ((pullback f).obj M)).inv ≫ (pullback f).obj M ◁ (pullbackObjUnitIso f).inv =
      (pullback f).map (ρ_ M).inv ≫ δ (pullback f) M (𝟙_ Y.Modules) := by
    rw [oplax_right_unitality (pullback f) M, pullback_η f]
    simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  simp only [uncurry', uncurry_eq, Functor.map_comp, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rw [Functor.ihomComparison_ev, ← Category.assoc (ρ_ _).inv, hu, Category.assoc,
    δ_natural_right_assoc]
  rw [Functor.Monoidal.δ_μ_assoc]

end AlgebraicGeometry.Scheme.Hom
