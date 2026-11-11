/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Rescaling continuous linear equivalences

A continuous linear equivalence `T : E ≃L[𝕜] F` over a field can be multiplied by a nonzero
scalar `d`; the result is again a continuous linear equivalence, whose inverse is `d⁻¹ • T⁻¹`.
The construction uses Mathlib's `ContinuousLinearEquiv.equivOfInverse'`.

Dually, multiplying a continuous linear map by a nonzero scalar `c` is composing it with the
scalar equivalence `ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)`, so results about
composition with equivalences apply to scalar multiples.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousConstSMul 𝕜 E]
  [ContinuousConstSMul 𝕜 F]

/-- Rescaling a continuous linear equivalence by a nonzero scalar `d` gives a continuous linear
equivalence, whose inverse is the inverse rescaled by `d⁻¹`. -/
theorem exists_coe_eq_smul (T : E ≃L[𝕜] F) {d : 𝕜} (hd : d ≠ 0) :
    ∃ U : E ≃L[𝕜] F, (U : E →L[𝕜] F) = d • (T : E →L[𝕜] F) ∧
      (U.symm : F →L[𝕜] E) = d⁻¹ • (T.symm : F →L[𝕜] E) :=
  ⟨.equivOfInverse' (d • (T : E →L[𝕜] F)) (d⁻¹ • (T.symm : F →L[𝕜] E))
    (by simp [smul_smul, hd]) (by simp [smul_smul, hd]), by simp, by simp⟩

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {𝕜 M M₂ : Type*} [Field 𝕜]
  [TopologicalSpace M] [AddCommMonoid M] [Module 𝕜 M]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module 𝕜 M₂] [ContinuousConstSMul 𝕜 M₂]

/-- Multiplying by a nonzero scalar is composing with the corresponding scalar equivalence. -/
theorem smul_eq_smulLeft_comp {c : 𝕜} (hc : c ≠ 0) (f : M →L[𝕜] M₂) :
    c • f = (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : M₂ ≃L[𝕜] M₂) ∘L f := by
  ext; simp

end ContinuousLinearMap
