/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Symmetric operators: negation and limits

Two facts about symmetric operators complementing Mathlib's
`Mathlib.Analysis.InnerProductSpace.Symmetric`:

* the negative of a symmetric linear map is symmetric (`LinearMap.IsSymmetric.neg`);
* the symmetric bounded operators form a closed subset of `E →L[𝕜] E`
  (`ContinuousLinearMap.isClosed_setOf_isSymmetric`), so a limit of symmetric bounded operators
  is symmetric. No completeness of `E` is needed: the condition `⟪T x, y⟫ = ⟪x, T y⟫` is closed
  in `T` for each pair `x, y`.
-/

public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

/-- The negative of a symmetric linear map is symmetric. -/
theorem IsSymmetric.neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : (-T).IsSymmetric := by
  simpa using IsSymmetric.zero.sub hT

end LinearMap

namespace ContinuousLinearMap

/-- The symmetric bounded operators form a closed subset of `E →L[𝕜] E`. -/
theorem isClosed_setOf_isSymmetric :
    IsClosed {T : E →L[𝕜] E | (T : E →ₗ[𝕜] E).IsSymmetric} := by
  simp only [LinearMap.IsSymmetric, coe_coe, Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
    isClosed_eq (by fun_prop) (by fun_prop)

end ContinuousLinearMap
