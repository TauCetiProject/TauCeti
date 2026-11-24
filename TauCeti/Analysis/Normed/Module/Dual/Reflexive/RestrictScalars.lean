/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.WeakSpace.RestrictScalars
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact

/-!
# Reflexivity under real scalar restriction

A real or complex seminormed space is reflexive over its scalar field exactly when its real
restriction is reflexive. Reflexivity here means surjectivity of the continuous bidual
inclusion. The characterization by weak compactness of the closed unit ball and the identity
`WeakSpace.restrictScalars` give this without completeness or separation assumptions.

Together with scalar independence of weak lower semicontinuity, this permits the real direct
method to be applied on complex reflexive spaces without changing the admissible sets or energy.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6 (reflexivity).
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Reflexivity over real or complex scalars agrees with reflexivity of the real restriction.
Neither completeness nor separation is assumed. -/
theorem surjective_inclusionInDoubleDual_iff_real :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E) ↔
      Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  rw [surjective_inclusionInDoubleDual_iff_isCompact_toWeakSpace_closedBall,
    surjective_inclusionInDoubleDual_iff_isCompact_toWeakSpace_closedBall]
  exact isCompact_toWeakSpace_iff_real

end TauCeti
