/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Topology.Algebra.SeparationQuotient.Section

/-!
# Operator norms of separation-quotient maps and sections

For a seminormed space `E` over a division ring `𝕜` with continuous scalar multiplication, the
continuous linear section `SeparationQuotient.outCLM 𝕜 E : SeparationQuotient E →L[𝕜] E` of
`SeparationQuotient.mkCLM 𝕜 E` preserves vector norms (`SeparationQuotient.norm_outCLM_apply`). Over
a nontrivially normed field `𝕜`, both `SeparationQuotient.mkCLM 𝕜 E` and
`SeparationQuotient.outCLM 𝕜 E` therefore have operator norm at most `1`
(`SeparationQuotient.norm_mkCLM_le`, `SeparationQuotient.norm_outCLM_le`).

For any bounded semilinear map `f : E →SL[σ₁₂] F` between seminormed spaces over nontrivially normed
fields, postcomposing with `SeparationQuotient.mkCLM` and precomposing with
`SeparationQuotient.outCLM` preserve the operator norm (`ContinuousLinearMap.norm_mkCLM_comp`,
`ContinuousLinearMap.norm_comp_outCLM`), and factoring `f` through `outCLM ∘ mkCLM` on either side
changes `f` by an operator of norm zero (`ContinuousLinearMap.norm_sub_outCLM_comp_mkCLM_comp`,
`ContinuousLinearMap.norm_sub_comp_outCLM_comp_mkCLM`).

## Main results

* `SeparationQuotient.norm_outCLM_apply`, `SeparationQuotient.nnNorm_outCLM_apply`:
  `‖outCLM 𝕜 E x‖ = ‖x‖` and `‖outCLM 𝕜 E x‖₊ = ‖x‖₊`.
* `SeparationQuotient.norm_mkCLM_le`, `SeparationQuotient.nnNorm_mkCLM_le`:
  `‖mkCLM 𝕜 E‖ ≤ 1` and `‖mkCLM 𝕜 E‖₊ ≤ 1`.
* `SeparationQuotient.norm_outCLM_le`, `SeparationQuotient.nnNorm_outCLM_le`:
  `‖outCLM 𝕜 E‖ ≤ 1` and `‖outCLM 𝕜 E‖₊ ≤ 1`.
* `ContinuousLinearMap.norm_mkCLM_comp`, `ContinuousLinearMap.nnNorm_mkCLM_comp`:
  `‖mkCLM 𝕜₂ F ∘SL f‖ = ‖f‖` and `‖mkCLM 𝕜₂ F ∘SL f‖₊ = ‖f‖₊`.
* `ContinuousLinearMap.norm_comp_outCLM`, `ContinuousLinearMap.nnNorm_comp_outCLM`:
  `‖f ∘SL outCLM 𝕜 E‖ = ‖f‖` and `‖f ∘SL outCLM 𝕜 E‖₊ = ‖f‖₊`.
* `ContinuousLinearMap.norm_sub_outCLM_comp_mkCLM_comp`,
  `ContinuousLinearMap.nnNorm_sub_outCLM_comp_mkCLM_comp`,
  `ContinuousLinearMap.norm_sub_comp_outCLM_comp_mkCLM`,
  `ContinuousLinearMap.nnNorm_sub_comp_outCLM_comp_mkCLM`:
  factoring `f` through `outCLM` and `mkCLM` on the codomain or domain changes `f` by an operator of
  norm zero.
-/

public section

open scoped NNReal

namespace SeparationQuotient

section Pointwise

variable {𝕜 E : Type*} [DivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-- `SeparationQuotient.outCLM` preserves norms. -/
@[simp]
theorem norm_outCLM_apply (x : SeparationQuotient E) : ‖outCLM 𝕜 E x‖ = ‖x‖ := by
  rw [← norm_mk, mk_outCLM]

/-- `SeparationQuotient.outCLM` preserves nonnegative norms. -/
@[simp]
theorem nnNorm_outCLM_apply (x : SeparationQuotient E) : ‖outCLM 𝕜 E x‖₊ = ‖x‖₊ :=
  Subtype.ext (norm_outCLM_apply x)

end Pointwise

section OpNorm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The separation-quotient projection `SeparationQuotient.mkCLM 𝕜 E` has operator norm at most
`1`. -/
theorem norm_mkCLM_le : ‖mkCLM 𝕜 E‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simp

/-- The separation-quotient projection `SeparationQuotient.mkCLM 𝕜 E` has nonnegative operator norm
at most `1`. -/
theorem nnNorm_mkCLM_le : ‖mkCLM 𝕜 E‖₊ ≤ 1 := by
  exact_mod_cast norm_mkCLM_le

/-- The continuous linear section `SeparationQuotient.outCLM 𝕜 E` has operator norm at most `1`. -/
theorem norm_outCLM_le : ‖outCLM 𝕜 E‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simp

/-- The continuous linear section `SeparationQuotient.outCLM 𝕜 E` has nonnegative operator norm at
most `1`. -/
theorem nnNorm_outCLM_le : ‖outCLM 𝕜 E‖₊ ≤ 1 := by
  exact_mod_cast norm_outCLM_le

end OpNorm

end SeparationQuotient

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

omit [RingHomIsometric σ₁₂] in
/-- Postcomposing a bounded semilinear map with `SeparationQuotient.mkCLM` preserves its operator
norm. -/
@[simp]
theorem norm_mkCLM_comp (f : E →SL[σ₁₂] F) :
    ‖SeparationQuotient.mkCLM 𝕜₂ F ∘SL f‖ = ‖f‖ := by
  simp only [norm_def, comp_apply, SeparationQuotient.mkCLM_apply, SeparationQuotient.norm_mk]

/-- Postcomposing a bounded semilinear map with `SeparationQuotient.mkCLM` preserves its nonnegative
operator norm. -/
@[simp]
theorem nnNorm_mkCLM_comp (f : E →SL[σ₁₂] F) :
    ‖SeparationQuotient.mkCLM 𝕜₂ F ∘SL f‖₊ = ‖f‖₊ :=
  Subtype.ext (norm_mkCLM_comp f)

omit [RingHomIsometric σ₁₂] in
/-- Precomposing a bounded semilinear map with `SeparationQuotient.outCLM` preserves its operator
norm. -/
@[simp]
theorem norm_comp_outCLM (f : E →SL[σ₁₂] F) :
    ‖f ∘SL SeparationQuotient.outCLM 𝕜 E‖ = ‖f‖ := by
  rw [norm_def, norm_def]
  congr 1; ext c
  refine and_congr_right fun _ ↦ SeparationQuotient.surjective_mk.forall.trans
    (forall_congr' fun x ↦ ?_)
  have hinsep : Inseparable (SeparationQuotient.outCLM 𝕜 E (SeparationQuotient.mk x)) x :=
    SeparationQuotient.mk_eq_mk.mp (SeparationQuotient.mk_outCLM _ _)
  rw [comp_apply, (hinsep.map f.continuous).norm_eq_norm, SeparationQuotient.norm_mk]

/-- Precomposing a bounded semilinear map with `SeparationQuotient.outCLM` preserves its nonnegative
operator norm. -/
@[simp]
theorem nnNorm_comp_outCLM (f : E →SL[σ₁₂] F) :
    ‖f ∘SL SeparationQuotient.outCLM 𝕜 E‖₊ = ‖f‖₊ :=
  Subtype.ext (norm_comp_outCLM f)

omit [RingHomIsometric σ₁₂] in
/-- Replacing a bounded semilinear map `f` by `outCLM ∘ mkCLM ∘ f` changes it by an operator of
norm zero. -/
theorem norm_sub_outCLM_comp_mkCLM_comp (f : E →SL[σ₁₂] F) :
    ‖f - SeparationQuotient.outCLM 𝕜₂ F ∘SL SeparationQuotient.mkCLM 𝕜₂ F ∘SL f‖ = 0 := by
  rw [← norm_mkCLM_comp]
  have hzero : SeparationQuotient.mkCLM 𝕜₂ F ∘SL
      (f - SeparationQuotient.outCLM 𝕜₂ F ∘SL SeparationQuotient.mkCLM 𝕜₂ F ∘SL f) = 0 := by
    ext x
    simp
  rw [hzero, opNorm_zero]

/-- Replacing a bounded semilinear map `f` by `outCLM ∘ mkCLM ∘ f` changes it by an operator of
nonnegative norm zero. -/
theorem nnNorm_sub_outCLM_comp_mkCLM_comp (f : E →SL[σ₁₂] F) :
    ‖f - SeparationQuotient.outCLM 𝕜₂ F ∘SL SeparationQuotient.mkCLM 𝕜₂ F ∘SL f‖₊ = 0 :=
  Subtype.ext (norm_sub_outCLM_comp_mkCLM_comp f)

omit [RingHomIsometric σ₁₂] in
/-- Replacing a bounded semilinear map `f` by `(f ∘ outCLM) ∘ mkCLM` changes it by an operator of
norm zero. -/
theorem norm_sub_comp_outCLM_comp_mkCLM (f : E →SL[σ₁₂] F) :
    ‖f - (f ∘SL SeparationQuotient.outCLM 𝕜 E) ∘SL SeparationQuotient.mkCLM 𝕜 E‖ = 0 := by
  refine le_antisymm (opNorm_le_bound _ le_rfl fun x ↦ ?_) (opNorm_nonneg _)
  have hx : ‖x - SeparationQuotient.outCLM 𝕜 E (SeparationQuotient.mk x)‖ = 0 := by
    rw [← SeparationQuotient.norm_mk]
    simp
  have hsub : (f - (f ∘SL SeparationQuotient.outCLM 𝕜 E) ∘SL SeparationQuotient.mkCLM 𝕜 E) x =
      f (x - SeparationQuotient.outCLM 𝕜 E (SeparationQuotient.mk x)) := by
    simp
  rw [hsub, norm_image_of_norm_eq_zero f f.cont hx, zero_mul]

/-- Replacing a bounded semilinear map `f` by `(f ∘ outCLM) ∘ mkCLM` changes it by an operator of
nonnegative norm zero. -/
theorem nnNorm_sub_comp_outCLM_comp_mkCLM (f : E →SL[σ₁₂] F) :
    ‖f - (f ∘SL SeparationQuotient.outCLM 𝕜 E) ∘SL SeparationQuotient.mkCLM 𝕜 E‖₊ = 0 :=
  Subtype.ext (norm_sub_comp_outCLM_comp_mkCLM f)

end ContinuousLinearMap
