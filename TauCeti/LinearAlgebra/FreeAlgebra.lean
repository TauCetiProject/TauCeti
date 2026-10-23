/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeAlgebra

/-!
# Word basis vectors of a free algebra

Mathlib's free-monoid basis vector is the ordered product of the generators in its word.
This identity converts basis evaluations into ordered word products, for instance when
proving that word moments determine a linear functional on a free algebra.
-/

public section

namespace TauCeti

/-- A free-monoid basis vector is the ordered product of the generators in its word. -/
@[simp]
theorem basisFreeMonoid_apply (R ι : Type*) [CommSemiring R] (w : FreeMonoid ι) :
    FreeAlgebra.basisFreeMonoid R ι w = (w.toList.map (FreeAlgebra.ι R)).prod := by
  simp [FreeAlgebra.basisFreeMonoid, FreeAlgebra.equivMonoidAlgebraFreeMonoid,
    FreeMonoid.lift_apply]

end TauCeti
