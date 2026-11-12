/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Extending closed subschemes across open immersions

The schematic closure of a closed subscheme across a quasi-compact open immersion
(a retrocompact open) restricts back to the original closed subscheme, with its full scheme
structure. In ideal-sheaf language, pushforward along a quasi-compact open immersion is a
right inverse to pullback.

Taking schematic closure also preserves avoidance of an open subset of the ambient scheme.
These facts allow one to extend the centre of a blowup without introducing a centre on an
open subset that must remain unchanged.

## References

* The Stacks Project, Section 29.6, *Scheme theoretic image* (tag 01R5).
* The Stacks Project, Section 38.33, *Nagata compactification* (tag 0F41).
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The schematic closure of a closed subscheme across a quasi-compact open immersion
(a retrocompact open) restricts to that same closed subscheme, including its nilpotents. -/
@[simp]
theorem comap_map_of_isOpenImmersion (I : X.IdealSheafData) (j : X ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] : (I.map j).comap j = I := by
  have h : IsPullback I.subschemeι (𝟙 _) j (I.subschemeι ≫ j) :=
    .of_vert_isIso_mono ⟨by simp⟩
  apply IdealSheafData.ext
  funext U
  rw [ideal_comap_of_isOpenImmersion, map]
  simpa only [ker_subschemeι] using
    (ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _ h U).symm

/-- A schematic image avoids an open subset precisely when the original closed subscheme
avoids its inverse image. The morphism need not be an immersion. -/
theorem disjoint_support_map_iff (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.Opens) :
    Disjoint (U : Set Y) ((I.map f).support : Set Y) ↔
      Disjoint (f ⁻¹' (U : Set Y)) (I.support : Set X) := by
  rw [support_map, TopologicalSpace.Closeds.coe_closure]
  constructor
  · intro h
    exact Set.disjoint_image_right.mp (h.mono_right subset_closure)
  · intro h
    exact (Set.disjoint_image_right.mpr h).closure_right U.isOpen

end AlgebraicGeometry.Scheme.IdealSheafData
