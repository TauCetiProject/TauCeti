/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Points of glued presheafed spaces

For glue data `D` of presheafed spaces, two points of the charts `U i` and `U j` have the same
image in the glued space exactly when they come from a common point of the overlap `V i j`, that
is, when they are related by `D.toTopGlueData.Rel`. This is the statement
`TopCat.GlueData.ι_eq_iff_rel` for the underlying glue data of topological spaces, transported
along the identification of the underlying space of the glued presheafed space with the glued
topological space. It is the presheafed-space counterpart of
`AlgebraicGeometry.Scheme.GlueData.ι_eq_iff`, and is how data defined chartwise on a glued space
is shown to be well defined.

## Main results

* `AlgebraicGeometry.PresheafedSpace.GlueData.ι_eq_iff_rel`: `ι i x = ι j y` if and only if `x`
  and `y` come from a common point of `V i j`.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.PresheafedSpace.GlueData

universe v u

variable {C : Type u} [Category.{v} C] (D : GlueData.{v, u} C) [HasLimits C]

local notation "𝖣" => D.toGlueData

/-- **Points with the same image in a glued presheafed space.** Points `x` of `U i` and `y` of
`U j` have the same image in the glued space if and only if there is a point `z` of `V i j` with
`f i j z = x` and `f j i (t i j z) = y`. -/
theorem ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
    (𝖣.ι i).base x = (𝖣.ι j).base y ↔ D.toTopGlueData.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  -- the chart maps of the glued presheafed space are those of the glued topological space,
  -- followed by the identification of the two glued spaces
  have key (k : D.J) (z : D.U k) : (𝖣.gluedIso (PresheafedSpace.forget C)).inv
      (D.toTopGlueData.ι k z) = (𝖣.ι k).base z :=
    ConcreteCategory.congr_hom (𝖣.ι_gluedIso_inv (PresheafedSpace.forget C) k) z
  rw [← key i x, ← key j y]
  exact ((TopCat.mono_iff_injective _).mp inferInstance).eq_iff.trans
    (D.toTopGlueData.ι_eq_iff_rel i j x y)

end AlgebraicGeometry.PresheafedSpace.GlueData
