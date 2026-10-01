/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dimension of a Euclidean space with a nonzero vector

This lemma derives positive ambient dimension from a nonzero vector. In particular, a nonzero
displacement supplies the dimension hypothesis needed for Newtonian-kernel monotonicity and
Poisson-kernel positivity.
-/

public section

namespace TauCeti

/-- A nonzero vector in `EuclideanSpace ℝ (Fin n)` forces the dimension to be positive. -/
theorem pos_of_ne_zero_euclideanSpace {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) : 0 < n := by
  have := nontrivial_of_ne x 0 hx
  simpa using Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ (Fin n))

end TauCeti

end
