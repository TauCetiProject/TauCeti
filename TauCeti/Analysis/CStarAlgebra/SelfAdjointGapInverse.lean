/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Spectral intervals and the gap inverse of a self-adjoint element

Let `a` be a self-adjoint element of a real normed star algebra with an isometric continuous
functional calculus for self-adjoint elements, for instance a C⋆-algebra. The norm of `a` is the
largest absolute value of a point of its real spectrum. Hence, for `0 ≤ r`, `‖a‖ ≤ r` exactly
when the real spectrum of `a` lies in the interval `[-r, r]`; this turns spectral localisation
into norm bounds and back.

If instead the spectrum has a gap around zero of radius `r > 0`, then `a` is invertible and
its canonical ring inverse has norm at most `r⁻¹`. This holds for any isometric continuous
functional calculus over `ℝ` or `ℂ`, so in particular for normal elements of a C⋆-algebra. This
quantitative bound is used in interval and exterior Sylvester estimates.

## Main results

* `IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`: for `0 ≤ r`, `‖a‖ ≤ r` if and only if
  `spectrum ℝ a ⊆ Set.Icc (-r) r`.
* `IsometricContinuousFunctionalCalculus.isUnit_and_norm_ringInverse_le` provides both `IsUnit a`
  and the norm bound for `Ring.inverse a` when every point of the spectrum has norm at least
  `r > 0`.
* `IsSelfAdjoint.isUnit_and_norm_ringInverse_le` is the special case of a self-adjoint element
  and its real spectrum.

## Source

The gap inverse is adapted from the Davis--Kahan/DKPS formalization (Kitware, Inc.),
`ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean` at commit
`fc38eb4`, by Jon Crall and Claude Fable 5 (Apache 2.0).
-/

public section

namespace IsometricContinuousFunctionalCalculus

variable {𝕜 A : Type*} {p : outParam (A → Prop)} [RCLike 𝕜] [NormedRing A] [StarRing A]
  [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p] {a : A} {r : ℝ}

/-- If every point of the spectrum of `a` has norm at least `r > 0`, then `a` is a unit and its
canonical ring inverse has norm at most `r⁻¹`. -/
theorem isUnit_and_norm_ringInverse_le (ha : p a) (hr : 0 < r)
    (hσ : ∀ x ∈ spectrum 𝕜 a, r ≤ ‖x‖) :
    IsUnit a ∧ ‖Ring.inverse a‖ ≤ r⁻¹ := by
  have hunit : IsUnit a :=
    spectrum.isUnit_of_zero_notMem 𝕜 fun h0 => hr.not_ge <| by simpa using hσ 0 h0
  refine ⟨hunit, ?_⟩
  rw [← cfc_ringInverse_id (R := 𝕜) a hunit]
  refine norm_cfc_le (by positivity) fun x hx => ?_
  rw [norm_inv]
  exact inv_anti₀ hr (hσ x hx)

end IsometricContinuousFunctionalCalculus

namespace IsSelfAdjoint

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A} {r : ℝ}

/-- The norm of a self-adjoint element is at most `r ≥ 0` exactly when its real spectrum lies
in the interval `[-r, r]`. -/
theorem norm_le_iff_spectrum_subset_Icc (ha : IsSelfAdjoint a) (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (-r) r := by
  simpa [Set.subset_def, abs_le, cfc_id' ℝ a] using norm_cfc_le_iff (id : ℝ → ℝ) a hr

/-- A positive gap around zero in the real spectrum of a self-adjoint element
makes it a unit and bounds the canonical ring inverse by the reciprocal gap. -/
theorem isUnit_and_norm_ringInverse_le (ha : IsSelfAdjoint a) (hr : 0 < r)
    (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) :
    IsUnit a ∧ ‖Ring.inverse a‖ ≤ r⁻¹ :=
  IsometricContinuousFunctionalCalculus.isUnit_and_norm_ringInverse_le ha hr hσ

end IsSelfAdjoint
