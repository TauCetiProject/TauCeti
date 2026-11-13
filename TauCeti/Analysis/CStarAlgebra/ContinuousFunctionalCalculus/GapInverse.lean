/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# The gap inverse under an isometric continuous functional calculus

Let `a` satisfy the predicate `p` of an isometric continuous functional calculus over `𝕜 = ℝ` or
`ℂ`. If the spectrum of `a` has a gap around zero of radius `r > 0`, that is, every point of
`spectrum 𝕜 a` has norm at least `r`, then `a` is invertible and its canonical ring inverse has
norm at most `r⁻¹`. This applies, for example, to self-adjoint elements of a C⋆-algebra and their
real spectrum, where the hypothesis reads `r ≤ |x|`, and to normal elements of a complex
C⋆-algebra. This quantitative bound is used in interval and exterior Sylvester estimates.

## Main results

* `IsometricContinuousFunctionalCalculus.isUnit_and_norm_ringInverse_le` provides both `IsUnit a`
  and the norm bound for `Ring.inverse a` when every point of the spectrum has norm at least
  `r > 0`.

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
