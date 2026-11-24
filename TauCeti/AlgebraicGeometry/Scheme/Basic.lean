/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Images of sets under morphisms of schemes

Basic facts about the set-theoretic images of subsets of the underlying space of a scheme under
morphisms of schemes.

## Main results

* `AlgebraicGeometry.Scheme.Hom.image_comp`: the image under a composite is the image of the
  image.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}}

/-- The image of a set under a composite of morphisms of schemes is the image of its image. -/
theorem image_comp (f : X ⟶ Y) (g : Y ⟶ Z) (s : Set X) : (f ≫ g) '' s = g '' (f '' s) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]

end AlgebraicGeometry.Scheme.Hom
