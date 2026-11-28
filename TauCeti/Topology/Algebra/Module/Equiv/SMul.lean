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
equivalence of a group element `g` is `g • id`, and its inverse is `g⁻¹ • id`
(`ContinuousLinearEquiv.coe_smulLeft`, `ContinuousLinearEquiv.coe_smulLeft_symm`), for any group
acting as `smulLeft` requires.
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

variable {R S M M₂ : Type*} [Semiring R] [GroupWithZero S]
  [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  [DistribMulAction S M₂] [SMulCommClass R S M₂] [ContinuousConstSMul S M₂]

/-- Multiplying by a nonzero commuting scalar is composing with the corresponding scalar
equivalence. -/
theorem smul_eq_smulLeft_comp {c : S} (hc : c ≠ 0) (f : M →L[R] M₂) :
    c • f = ((letI := SMulCommClass.symm R S M₂
      ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)) : M₂ ≃L[R] M₂) ∘L f := by
  have := SMulCommClass.symm R S M₂
  ext; simp

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {R M G : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [Group G] [DistribMulAction G M] [ContinuousConstSMul G M] [SMulCommClass G R M]

/-- The scalar equivalence `smulLeft g` of a group element `g` is `g • id` as a continuous linear
map. The action of `G` on continuous linear maps uses `SMulCommClass.symm`. -/
theorem coe_smulLeft (g : G) :
    haveI := SMulCommClass.symm G R M
    ((smulLeft g : M ≃L[R] M) : M →L[R] M) = g • ContinuousLinearMap.id R M := by
  ext v
  rw [coe_coe, smulLeft_apply_apply, _root_.smul_apply, ContinuousLinearMap.id_apply]

/-- The inverse of the scalar equivalence `smulLeft g` is `g⁻¹ • id` as a continuous linear map. -/
theorem coe_smulLeft_symm (g : G) :
    haveI := SMulCommClass.symm G R M
    (((smulLeft g : M ≃L[R] M).symm : M ≃L[R] M) : M →L[R] M) =
      g⁻¹ • ContinuousLinearMap.id R M := by
  ext v
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply, coe_coe, symm_apply_eq,
    smulLeft_apply_apply, smul_inv_smul]

end ContinuousLinearEquiv
