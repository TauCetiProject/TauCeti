/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Spectral intervals of a self-adjoint element

Let `a` be a self-adjoint element of a real normed star algebra with an isometric continuous
functional calculus for self-adjoint elements, for instance a C⋆-algebra. Every point of the real
spectrum of `a` has absolute value at most `‖a‖`
(`IsometricContinuousFunctionalCalculus.norm_spectrum_le`). When the algebra is nontrivial, `‖a‖`
is attained as the largest such absolute value
(`IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum`); in a trivial algebra the
spectrum is empty and `‖a‖ = 0`. In either case, for `0 ≤ r`, `‖a‖ ≤ r` exactly when the real
spectrum of `a` lies in the interval `[-r, r]`; this turns spectral localisation into norm bounds
and back.

If instead the spectrum has a gap around zero of radius `r > 0`, then `a` is invertible and its
canonical ring inverse has norm at most `r⁻¹`; this is
`IsometricContinuousFunctionalCalculus.isUnit_and_norm_ringInverse_le` in
`TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.GapInverse`, which applies to `a`
and its real spectrum directly.

## Main results

* `IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`: for `0 ≤ r`, `‖a‖ ≤ r` if and only if
  `spectrum ℝ a ⊆ Set.Icc (-r) r`.
-/

public section

namespace IsSelfAdjoint

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A} {r : ℝ}

/-- The norm of a self-adjoint element is at most `r ≥ 0` exactly when its real spectrum lies
in the interval `[-r, r]`. -/
theorem norm_le_iff_spectrum_subset_Icc (ha : IsSelfAdjoint a) (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (-r) r := by
  simpa [Set.subset_def, abs_le, cfc_id' ℝ a] using norm_cfc_le_iff (id : ℝ → ℝ) a hr

end IsSelfAdjoint
