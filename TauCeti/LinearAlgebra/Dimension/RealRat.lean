/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Hamel bases of `ℝ` over `ℚ`

A Hamel basis of `ℝ` over `ℚ` has at least two elements: its cardinality is `Module.rank ℚ ℝ`,
which is the continuum by Mathlib's `Real.rank_rat_real`.
-/

public section

namespace Real

/-- A Hamel basis of `ℝ` over `ℚ` has at least two elements. -/
instance nontrivial_ofVectorSpaceIndex_rat_real :
    Nontrivial (Module.Basis.ofVectorSpaceIndex ℚ ℝ) := by
  rw [← Cardinal.one_lt_iff_nontrivial, (Module.Basis.ofVectorSpace ℚ ℝ).mk_eq_rank'',
    Real.rank_rat_real]
  exact_mod_cast Cardinal.nat_lt_continuum 1

end Real
