/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Dimensions of Euclidean spaces

The first lemma derives positive ambient dimension from a nonzero vector. In particular, a nonzero
displacement supplies the dimension hypothesis needed for Newtonian-kernel monotonicity and
Poisson-kernel positivity.

The instance `TauCeti.factFinrankEuclideanSpaceComplex` records the real dimension of `ℂᵏ⁺¹` as
`(2k + 1) + 1`. This is the form of the hypothesis `Fact (finrank ℝ E = n + 1)` under which
Mathlib puts a manifold structure on the unit sphere of `E`
(`EuclideanSpace.instChartedSpaceSphere`), so instance search finds the sphere of `ℂᵏ⁺¹`, and its
quotients, to be manifolds of dimension `2k + 1`.
-/

public section

namespace TauCeti

/-- A nonzero vector in `EuclideanSpace ℝ (Fin n)` forces the dimension to be positive. -/
theorem pos_of_ne_zero_euclideanSpace {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) : 0 < n := by
  have := nontrivial_of_ne x 0 hx
  simpa using Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ (Fin n))

/-- The real dimension of `ℂᵏ⁺¹` is `2k + 2`, written as `(2k + 1) + 1` so that its unit sphere,
and quotients of the sphere, are found to be manifolds of dimension `2k + 1`. -/
instance factFinrankEuclideanSpaceComplex (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin (k + 1))) = 2 * k + 1 + 1) :=
  ⟨by rw [finrank_real_of_complex, finrank_euclideanSpace_fin]; ring⟩

end TauCeti

end
