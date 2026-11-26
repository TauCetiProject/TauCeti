/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Continuous linear maps on opposite modules

Precomposing a continuous linear map `M : A →L[𝕜] E` with `MulOpposite.unop` gives a continuous
linear map `ContinuousLinearMap.compUnop M : Aᵐᵒᵖ →L[𝕜] E`. This transports left or right
actions across `MulOpposite` without repeating the continuity or linearity bundling.

## Main definitions

* `ContinuousLinearMap.compUnop`: precomposition of a continuous linear map with
  `MulOpposite.unop`.

## Main results

* `ContinuousLinearMap.compUnop_eq_comp`: unfolding lemma for `compUnop`.
* `ContinuousLinearMap.compUnop_apply`: `M.compUnop a = M a.unop`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [Semiring 𝕜]
  [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- Precomposition of a continuous linear map `M : A →L[𝕜] E` with `MulOpposite.unop`. -/
def compUnop (M : A →L[𝕜] E) : Aᵐᵒᵖ →L[𝕜] E :=
  M.comp (MulOpposite.opContinuousLinearEquiv 𝕜 (M := A)).symm.toContinuousLinearMap

/-- Unfolding lemma for `ContinuousLinearMap.compUnop`. -/
theorem compUnop_eq_comp (M : A →L[𝕜] E) :
    M.compUnop =
      M.comp (MulOpposite.opContinuousLinearEquiv 𝕜 (M := A)).symm.toContinuousLinearMap := by
  unfold compUnop
  rfl

/-- Applying `M.compUnop` to `a : Aᵐᵒᵖ` evaluates `M` at `a.unop`. -/
@[simp]
theorem compUnop_apply (M : A →L[𝕜] E) (a : Aᵐᵒᵖ) : M.compUnop a = M a.unop := by
  unfold compUnop
  rfl

end ContinuousLinearMap
