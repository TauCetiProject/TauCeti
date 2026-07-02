/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Elementary bilinear-form identities

This file records small general identities for `LinearMap.BilinForm` that are useful across
several subjects.
-/

public section

namespace TauCeti

namespace LinearMap

namespace BilinForm

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {B : _root_.LinearMap.BilinForm R M}

/-- A symmetric bilinear form on a sum expands without division: the cross term appears twice. -/
theorem IsSymm.self_add (hB : B.IsSymm) (x y : M) :
    B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
  simp only [map_add, _root_.LinearMap.add_apply]
  rw [hB.eq y x]
  ring

end BilinForm

end LinearMap

end TauCeti
