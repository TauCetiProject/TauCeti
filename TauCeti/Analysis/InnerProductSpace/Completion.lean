/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Adjoints of operators extended to completions

A bounded operator `f : E →L[𝕜] F` between inner product spaces that need not be complete extends
to the bounded operator `f.completion` between the Hilbert space completions. Even when `f` has no
adjoint, because `E` or `F` is not complete, it may have a *formal adjoint*: an operator
`g : F →L[𝕜] E` with `⟪f x, y⟫ = ⟪x, g y⟫` for all `x` and `y`. The extension of `g` is then the
Hilbert space adjoint of the extension of `f` (`ContinuousLinearMap.adjoint_completion`), because
both sides of the defining identity are continuous and the spaces are dense in their completions.

This computes adjoints of operators on completed tensor products of Hilbert spaces, where the
algebraic tensor product is not complete.
-/

public section

open UniformSpace
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- If `g` is a formal adjoint of `f`, `⟪f x, y⟫ = ⟪x, g y⟫`, then the extension of `g` to the
completions is the adjoint of the extension of `f`. -/
theorem adjoint_completion {f : E →L[𝕜] F} {g : F →L[𝕜] E}
    (h : ∀ x y, ⟪f x, y⟫_𝕜 = ⟪x, g y⟫_𝕜) : adjoint f.completion = g.completion := by
  refine ((eq_adjoint_iff g.completion f.completion).2 fun y x ↦ ?_).symm
  induction y, x using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih y x =>
    simp only [completion_apply_coe, Completion.inner_coe]
    simpa only [inner_conj_symm] using (congrArg (starRingEnd 𝕜) (h x y)).symm

end ContinuousLinearMap
