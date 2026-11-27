/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Ultra

/-!
# Ultrametric normed fields from algebra maps

A normed field is ultrametric as soon as the image of some algebra's scalars lies in its
closed unit ball, since the natural numbers then lie there too. This is the algebra-map form
of Mathlib's `IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one`.
-/

public section

namespace IsUltrametricDist

/-- A normed field is ultrametric if an algebra's scalars lie in its closed unit ball. -/
theorem isUltrametricDist_of_forall_norm_algebraMap_le_one {R C : Type*}
    [CommSemiring R] [NormedField C] [Algebra R C]
    (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) : IsUltrametricDist C :=
  isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
    simpa using hR (n : R)

end IsUltrametricDist
