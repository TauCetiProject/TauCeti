/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive operators associated to contractions

A contraction between real or complex Hilbert spaces satisfies `D D† ≤ 1` in the Loewner
order. In particular, its defect operator `1 - D D†` is positive, so it admits a positive
square root whenever a continuous functional calculus is available.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A contraction composed with its adjoint is bounded above by the identity in the Loewner
order. Equivalently, its defect operator is positive. -/
theorem self_comp_adjoint_le_one (D : F →L[𝕜] E) (hD : ‖D‖ ≤ 1) :
    D ∘L D.adjoint ≤ 1 := by
  rw [le_def, isPositive_def']
  refine ⟨(IsSelfAdjoint.one _).sub (isPositive_self_comp_adjoint D).isSelfAdjoint, ?_⟩
  intro z
  have hz : ‖D.adjoint z‖ ≤ ‖z‖ := by
    simpa only [one_mul] using D.adjoint.le_of_opNorm_le (c := 1) (by simpa using hD) z
  simpa only [reApplyInnerSelf, sub_apply, one_apply_eq_self, inner_sub_left, comp_apply,
    ← D.adjoint_inner_right, map_sub, inner_self_eq_norm_sq] using
    sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hz 2)

end ContinuousLinearMap
