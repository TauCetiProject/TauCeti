/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Rescaling continuous linear equivalences

A continuous linear equivalence `T : E ≃L[𝕜] F` over a semifield can be multiplied by a nonzero
scalar `d`; the result is again a continuous linear equivalence, whose inverse is `d⁻¹ • T⁻¹`.
The construction uses Mathlib's `ContinuousLinearEquiv.equivOfInverse'`.

Dually, multiplying a continuous linear map by a nonzero scalar `c` is composing it with the
scalar equivalence `ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)`, so results about
composition with equivalences apply to scalar multiples. As a continuous linear map, the scalar
equivalence of `c ≠ 0` is `c • id`, and its inverse is `c⁻¹ • id`
(`ContinuousLinearEquiv.coe_smulLeft_mk0`, `ContinuousLinearEquiv.coe_smulLeft_mk0_symm`).
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [Semifield 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousConstSMul 𝕜 E]
  [ContinuousConstSMul 𝕜 F]

/-- Rescaling a continuous linear equivalence by a nonzero scalar `d` gives a continuous linear
equivalence, whose inverse is the inverse rescaled by `d⁻¹`. -/
theorem exists_coe_eq_smul (T : E ≃L[𝕜] F) {d : 𝕜} (hd : d ≠ 0) :
    ∃ U : E ≃L[𝕜] F, (U : E →L[𝕜] F) = d • (T : E →L[𝕜] F) ∧
      (U.symm : F →L[𝕜] E) = d⁻¹ • (T.symm : F →L[𝕜] E) :=
  ⟨.ofContinuousLinearMap (d • (T : E →L[𝕜] F)) (d⁻¹ • (T.symm : F →L[𝕜] E))
    (by simp [smul_smul, hd]) (by simp [smul_smul, hd]), by simp, by simp⟩

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {𝕜 M M₂ : Type*} [Semifield 𝕜]
  [TopologicalSpace M] [AddCommMonoid M] [Module 𝕜 M]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module 𝕜 M₂] [ContinuousConstSMul 𝕜 M₂]

/-- Multiplying by a nonzero scalar is composing with the corresponding scalar equivalence. -/
theorem smul_eq_smulLeft_comp {c : 𝕜} (hc : c ≠ 0) (f : M →L[𝕜] M₂) :
    c • f = (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : M₂ ≃L[𝕜] M₂) ∘L f := by
  ext; simp

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 M : Type*} [Semifield 𝕜] [TopologicalSpace M] [AddCommMonoid M] [Module 𝕜 M]
  [ContinuousConstSMul 𝕜 M]

/-- The scalar equivalence of a nonzero scalar `c` is `c • id` as a continuous linear map. -/
theorem coe_smulLeft_mk0 {c : 𝕜} (hc : c ≠ 0) :
    ((smulLeft (Units.mk0 c hc) : M ≃L[𝕜] M) : M →L[𝕜] M) = c • ContinuousLinearMap.id 𝕜 M := by
  rw [ContinuousLinearMap.smul_eq_smulLeft_comp hc, ContinuousLinearMap.comp_id]

/-- The inverse of the scalar equivalence of a nonzero scalar `c` is `c⁻¹ • id` as a continuous
linear map. -/
theorem coe_smulLeft_mk0_symm {c : 𝕜} (hc : c ≠ 0) :
    (((smulLeft (Units.mk0 c hc) : M ≃L[𝕜] M).symm : M ≃L[𝕜] M) : M →L[𝕜] M) =
      c⁻¹ • ContinuousLinearMap.id 𝕜 M := by
  ext v
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply, coe_coe, symm_apply_eq,
    smulLeft_apply_apply, Units.smul_def, Units.val_mk0, smul_inv_smul₀ hc]

end ContinuousLinearEquiv
