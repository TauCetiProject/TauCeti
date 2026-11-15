/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Group.ControlledClosure
public import Mathlib.Analysis.Normed.Group.HomCompletion
public import TauCeti.Analysis.Normed.Group.BallSphere
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Operator norms of bounded maps extended to completions

A bounded semilinear map `f : E →SL[σ₁₂] F` between seminormed spaces extends to the bounded
map `f.completion` between the completions, and, when `F` is complete and Hausdorff, to the
bounded map `f.fromCompletion` from the completion of `E` to `F`. Since `E` has dense image in
its completion and the canonical map preserves norms, neither extension changes the operator norm.

These are the continuous semilinear analogues of Mathlib's `NormedAddGroupHom.norm_completion`.
They make extension to completions an isometric operation, as needed for the norm-preserving
universal properties of completed normed constructions. Likewise, a linear isometric equivalence
extends to the linear isometric equivalence `e.completion` between the completions, the analogue
for equivalences of Mathlib's `LinearIsometry.completion`.

Extension to completions also preserves metric quotient maps. If `f` lifts every vector of norm
less than `r` to a vector of norm less than `r`, so does `f.completion`; the lifts in the
completion come from Mathlib's `controlled_closure_range_of_complete`. An operator of norm at most
one with this lifting property maps each open ball about `0` onto the open ball of the same radius
(`ContinuousLinearMap.image_ball_eq_ball`), so by `ContinuousLinearMap.norm_completion` its
extension to the completions has the same property.

## Main results

* `ContinuousLinearMap.norm_completion`: `‖f.completion‖ = ‖f‖`.
* `ContinuousLinearMap.norm_fromCompletion`: `‖f.fromCompletion‖ = ‖f‖`.
* `ContinuousLinearMap.norm_toComplL_comp` and `ContinuousLinearMap.eNorm_toComplL_comp`:
  composing with the embedding of the codomain into its completion preserves the operator norm.
* `ContinuousLinearMap.ball_subset_image_completion_ball` and
  `ContinuousLinearMap.image_completion_ball`: the extension of a metric quotient map to the
  completions is a metric quotient map.
* `LinearIsometryEquiv.completion`: the extension of a linear isometric equivalence to the
  completions.
* `LinearIsometryEquiv.toLinearIsometry_completion`: as a linear isometry, it is
  `LinearIsometry.completion`.
* `LinearIsometryEquiv.completion_symm`, `LinearIsometryEquiv.completion_refl`,
  `LinearIsometryEquiv.completion_trans`: extension to completions is compatible with inverses,
  identities and composites.
* `ContinuousLinearMap.completion_smul` and `ContinuousLinearMap.fromCompletion_smul`: extending a
  bounded semilinear map to completions preserves equivariance for an auxiliary scalar action.
* `LinearIsometry.surjective_fromCompletion_of_denseRange`: extending a linear isometry with dense
  range from a completion is surjective.
* `SeparationQuotient.norm_liftCLM`, `SeparationQuotient.liftCLM_smul`, and
  `SeparationQuotient.eq_liftCLM_iff`: operator-norm preservation, equivariance, and uniqueness for
  `SeparationQuotient.liftCLM`.
* `UniformSpace.Completion.completionSeparationQuotientₗᵢ`: the canonical linear isometric
  equivalence `Completion (SeparationQuotient E) ≃ₗᵢ[𝕜] Completion E` for a seminormed space `E`.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

omit [RingHomIsometric σ₁₂] in
/-- Extending a bounded semilinear map to the completions of its domain and codomain preserves
its operator norm. -/
@[simp]
theorem norm_completion (f : E →SL[σ₁₂] F) : ‖f.completion‖ = ‖f‖ := by
  rw [norm_def, norm_def]
  congr 1
  ext c
  refine and_congr_right fun _ ↦ ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · simpa only [completion_apply_coe, Completion.norm_coe] using h x
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [completion_apply_coe, Completion.norm_coe] using h x

omit [RingHomIsometric σ₁₂] in
/-- Extending a bounded semilinear map into a complete Hausdorff space to the completion of its
domain preserves its operator norm. -/
@[simp]
theorem norm_fromCompletion [T0Space F] [CompleteSpace F] (f : E →SL[σ₁₂] F) :
    ‖f.fromCompletion‖ = ‖f‖ := by
  rw [norm_def, norm_def]
  congr 1
  ext c
  refine and_congr_right fun _ ↦ ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · simpa only [fromCompletion_apply_coe, Completion.norm_coe] using h x
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [fromCompletion_apply_coe, Completion.norm_coe] using h x

/-- If `f` lifts every vector of norm less than `r` to a vector of norm less than `r`, then so
does its extension `f.completion` to the completions. -/
theorem ball_subset_image_completion_ball {f : E →SL[σ₁₂] F}
    (hf : ∀ r, Metric.ball (0 : F) r ⊆ f '' Metric.ball 0 r) (r : ℝ) :
    Metric.ball (0 : Completion F) r ⊆ f.completion '' Metric.ball 0 r := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  -- Choose `δ > 0` with `(1 + δ + δ) * ‖w‖ < r`.
  obtain ⟨δ, hδ, hδw⟩ := exists_pos_mul_lt (sub_pos.2 hw) (2 * ‖w‖)
  have hδr : (1 + δ + δ) * ‖w‖ < r := by linarith
  -- Points of `F` lift with constant `1 + δ`, so points of the completion lift with `1 + δ + δ`.
  let g := f.completion.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom ‖f.completion‖
    f.completion.le_opNorm
  have hyp (k : F) : ∃ x, g x = NormedAddCommGroup.toCompl k ∧ ‖x‖ ≤ (1 + δ) * ‖k‖ := by
    rcases (norm_nonneg k).eq_or_lt with hk | hk
    · refine ⟨0, ?_, by rw [norm_zero]; positivity⟩
      rw [map_zero, eq_comm, ← norm_eq_zero, NormedAddCommGroup.norm_toCompl, hk]
    · obtain ⟨x, hfx, hx⟩ := TauCeti.exists_apply_eq_norm_lt_add hf k (mul_pos hδ hk)
      refine ⟨x, ?_, by rw [Completion.norm_coe]; linarith⟩
      -- `g` is `f.completion` as a bundled normed group hom, so they agree by definition.
      change f.completion x = k
      rw [completion_apply_coe, hfx]
  obtain ⟨x, hx, hxw⟩ := controlled_closure_range_of_complete NormedAddCommGroup.norm_toCompl
    (by positivity) hδ hyp w (NormedAddCommGroup.denseRange_toCompl w)
  exact ⟨x, mem_ball_zero_iff.2 (hxw.trans_lt hδr), hx⟩

/-- The extension to the completions of a **metric quotient map** is a metric quotient map: if
`‖f‖ ≤ 1` and `f` lifts every vector of norm less than `r` to a vector of norm less than `r`,
then `f.completion` maps each open ball about `0` onto the open ball of the same radius. -/
theorem image_completion_ball {f : E →SL[σ₁₂] F} (hf₁ : ‖f‖ ≤ 1)
    (hf : ∀ r, Metric.ball (0 : F) r ⊆ f '' Metric.ball 0 r) (r : ℝ) :
    f.completion '' Metric.ball 0 r = Metric.ball 0 r :=
  image_ball_eq_ball (f.norm_completion.trans_le hf₁) (ball_subset_image_completion_ball hf) r

omit [RingHomIsometric σ₁₂] in
/-- Composing a bounded semilinear map with the embedding of its codomain into the completion does
not change its operator norm. -/
@[simp]
theorem norm_toComplL_comp (f : E →SL[σ₁₂] F) :
    ‖(Completion.toComplL : F →L[𝕜₂] Completion F) ∘SL f‖ = ‖f‖ := by
  simp only [norm_def, comp_apply, Completion.coe_toComplL, Completion.norm_coe]

/-- Composing a bounded semilinear map with the embedding of its codomain into the completion does
not change its operator `ℝ≥0∞`-norm. -/
@[simp]
theorem eNorm_toComplL_comp (f : E →SL[σ₁₂] F) :
    ‖(Completion.toComplL : F →L[𝕜₂] Completion F) ∘SL f‖ₑ = ‖f‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_toComplL_comp]

section SMulEquivariance

variable {R S A α β : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring S] [Module S α] [UniformContinuousConstSMul S α]
  [Semiring R] [UniformSpace β] [AddCommGroup β] [IsUniformAddGroup β]
  [Module R β] [UniformContinuousConstSMul R β] {σ : S →+* R}

/-- Extending a continuous semilinear map to completions preserves equivariance for an auxiliary
uniformly continuous scalar action. -/
theorem completion_smul [SMul A α] [UniformContinuousConstSMul A α]
    [SMul A β] [UniformContinuousConstSMul A β]
    (f : α →SL[σ] β) (hf : ∀ (a : A) (x : α), f (a • x) = a • f x) (a : A) (z : Completion α) :
    f.completion (a • z) = a • f.completion z :=
  Completion.induction_on z
    (isClosed_eq (f.completion.continuous.comp (continuous_const_smul a))
      ((continuous_const_smul a).comp f.completion.continuous))
    fun x ↦ by rw [← Completion.coe_smul, completion_apply_coe, hf, Completion.coe_smul,
      completion_apply_coe]

/-- Extending a continuous semilinear map into a complete Hausdorff group from the completion of its
domain preserves equivariance for an auxiliary scalar action. -/
theorem fromCompletion_smul [T0Space β] [CompleteSpace β]
    [SMul A α] [UniformContinuousConstSMul A α] [SMul A β] [ContinuousConstSMul A β]
    (f : α →SL[σ] β) (hf : ∀ (a : A) (x : α), f (a • x) = a • f x) (a : A) (z : Completion α) :
    f.fromCompletion (a • z) = a • f.fromCompletion z :=
  Completion.induction_on z
    (isClosed_eq (f.fromCompletion.continuous.comp (continuous_const_smul a))
      ((continuous_const_smul a).comp f.fromCompletion.continuous))
    fun x ↦ by rw [← Completion.coe_smul, fromCompletion_apply_coe, hf, fromCompletion_apply_coe]

end SMulEquivariance

end ContinuousLinearMap

namespace LinearIsometry

/-- If a linear isometry `f : E →ₛₗᵢ[σ₁₂] F` into a complete normed module has dense range, then its
extension `f.fromCompletion : Completion E →ₛₗᵢ[σ₁₂] F` is surjective. -/
theorem surjective_fromCompletion_of_denseRange {R R₂ E F : Type*}
    [Semiring R] [Semiring R₂] [SeminormedAddCommGroup E] [Module R E]
    [UniformContinuousConstSMul R E] [NormedAddCommGroup F] [Module R₂ F]
    [PseudoMetricSpace R₂] [CompleteSpace F] [IsBoundedSMul R₂ F] {σ₁₂ : R →+* R₂}
    (f : E →ₛₗᵢ[σ₁₂] F) (hf : DenseRange f) : Function.Surjective f.fromCompletion := by
  rw [← Set.range_eq_univ, ← Set.univ_subset_iff, ← hf.closure_eq]
  exact closure_minimal (by rintro _ ⟨x, rfl⟩; exact ⟨x, f.fromCompletion_apply_coe x⟩)
    f.fromCompletion.isometry.isUniformInducing.isComplete_range.isClosed

end LinearIsometry

namespace LinearIsometryEquiv

variable {𝕜 𝕜₂ E F : Type*} [NormedField 𝕜] [NormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Extend a linear isometric equivalence `e : E ≃ₛₗᵢ[σ₁₂] F` to a linear isometric equivalence
between the completions of `E` and `F`. -/
noncomputable def completion (e : E ≃ₛₗᵢ[σ₁₂] F) : Completion E ≃ₛₗᵢ[σ₁₂] Completion F :=
  e.toLinearEquiv.extendOfIsometry Completion.toComplₗᵢ.toLinearMap
    Completion.toComplₗᵢ.toLinearMap Completion.denseRange_coe Completion.denseRange_coe
    fun x ↦ by simp

/-- On `E`, the extension of `e` to the completions is `e`. -/
@[simp]
theorem completion_apply_coe (e : E ≃ₛₗᵢ[σ₁₂] F) (x : E) : e.completion x = e x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- On `F`, the inverse of the extension of `e` to the completions is `e.symm`. -/
theorem completion_symm_apply_coe (e : E ≃ₛₗᵢ[σ₁₂] F) (y : F) :
    e.completion.symm y = e.symm y :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ y

/-- The extension of `e` to the completions is `UniformSpace.Completion.map e`. -/
@[simp low]
theorem coe_completion (e : E ≃ₛₗᵢ[σ₁₂] F) : ⇑e.completion = Completion.map e :=
  Completion.ext e.completion.continuous Completion.continuous_map fun x ↦ by
    rw [completion_apply_coe, Completion.map_coe e.isometry.uniformContinuous]

/-- The inverse of the extension of `e` to the completions is the extension of `e.symm`. -/
@[simp]
theorem completion_symm (e : E ≃ₛₗᵢ[σ₁₂] F) : e.completion.symm = e.symm.completion := by
  ext y
  induction y using Completion.induction_on with
  | hp => exact isClosed_eq e.completion.symm.continuous e.symm.completion.continuous
  | ih y => rw [completion_symm_apply_coe, completion_apply_coe]

variable (𝕜 E) in
/-- The extension of the identity to the completion is the identity. -/
@[simp]
theorem completion_refl :
    (LinearIsometryEquiv.refl 𝕜 E).completion = LinearIsometryEquiv.refl 𝕜 (Completion E) := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (LinearIsometryEquiv.refl 𝕜 E).completion.continuous continuous_id
  | ih x => simp

/-- Extending a composite of linear isometric equivalences to the completions is the composite
of their extensions. -/
@[simp]
theorem completion_trans {𝕜₃ G : Type*} [NormedField 𝕜₃] [SeminormedAddCommGroup G]
    [NormedSpace 𝕜₃ G] {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₃₂ : 𝕜₃ →+* 𝕜₂} {σ₁₃ : 𝕜 →+* 𝕜₃}
    {σ₃₁ : 𝕜₃ →+* 𝕜} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] (e : E ≃ₛₗᵢ[σ₁₂] F) (e' : F ≃ₛₗᵢ[σ₂₃] G) :
    (e.trans e').completion = e.completion.trans e'.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (e.trans e').completion.continuous
      (e.completion.trans e'.completion).continuous
  | ih x => simp

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- As a linear isometry, the extension of `e` to the completions is the extension
`LinearIsometry.completion` of `e` viewed as a linear isometry. -/
@[simp]
theorem toLinearIsometry_completion (e : E ≃ₛₗᵢ[σ₁₂] F) :
    e.completion.toLinearIsometry = e.toLinearIsometry.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq e.completion.continuous e.toLinearIsometry.completion.continuous
  | ih x => simp [LinearIsometry.completion_apply_coe]

end NormedAddCommGroup

end LinearIsometryEquiv

namespace SeparationQuotient

section Module

variable {R S A M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [Semiring S] [AddCommMonoid N] [Module S N] [TopologicalSpace N] {σ : R →+* S}

/-- Lifting a continuous semilinear map to `SeparationQuotient M` preserves equivariance for an
auxiliary continuous scalar action. -/
theorem liftCLM_smul [SMul A M] [ContinuousConstSMul A M] [SMul A N]
    (f : M →SL[σ] N) (hf_insep : ∀ x y, Inseparable x y → f x = f y)
    (hf_smul : ∀ (a : A) (x : M), f (a • x) = a • f x) (a : A) (z : SeparationQuotient M) :
    liftCLM f hf_insep (a • z) = a • liftCLM f hf_insep z := by
  rcases surjective_mk z with ⟨x, rfl⟩; rw [← mk_smul, liftCLM_mk, liftCLM_mk, hf_smul]

/-- Uniqueness in the universal property of `SeparationQuotient M` for continuous semilinear
maps. -/
theorem eq_liftCLM_iff (f : M →SL[σ] N) (hf_insep : ∀ x y, Inseparable x y → f x = f y)
    (g : SeparationQuotient M →SL[σ] N) :
    g = liftCLM f hf_insep ↔ ∀ x : M, g (mk x) = f x :=
  ⟨fun h x ↦ by rw [h, liftCLM_mk],
    fun h ↦ ContinuousLinearMap.ext <| surjective_mk.forall.2 fun x ↦ by rw [h, liftCLM_mk]⟩

end Module

section Norm

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Lifting a bounded semilinear map to the separation quotient of its domain preserves its
operator norm. -/
@[simp]
theorem norm_liftCLM (f : E →SL[σ₁₂] F) (hf : ∀ x y, Inseparable x y → f x = f y) :
    ‖liftCLM f hf‖ = ‖f‖ := by
  rw [ContinuousLinearMap.norm_def, ContinuousLinearMap.norm_def]
  congr 1; ext c
  refine and_congr_right fun _ ↦ ⟨fun h x ↦ ?_, fun h ↦ surjective_mk.forall.2 fun x ↦ ?_⟩
  · simpa only [liftCLM_mk, norm_mk] using h (mk x)
  · simpa only [liftCLM_mk, norm_mk] using h x

end Norm

/-- Uniformly continuous scalar multiplication descends to the separation quotient. -/
instance instUniformContinuousConstSMul {M X : Type*} [UniformSpace X] [SMul M X]
    [UniformContinuousConstSMul M X] : UniformContinuousConstSMul M (SeparationQuotient X) :=
  ⟨fun b ↦ uniformContinuous_dom.2 <| by
    simpa only [Function.comp_def, ← mk_smul] using
      uniformContinuous_mk.comp (uniformContinuous_const_smul b)⟩

end SeparationQuotient

namespace UniformSpace.Completion

variable (𝕜 E : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

private noncomputable def liftToComplₗᵢ : SeparationQuotient E →ₗᵢ[𝕜] Completion E :=
  { SeparationQuotient.liftCLM (toComplL : E →L[𝕜] Completion E)
      fun _ _ h ↦ (h.map (toComplL : E →L[𝕜] Completion E).continuous).eq with
    norm_map' := SeparationQuotient.surjective_mk.forall.2 fun _ ↦ by
      simp [SeparationQuotient.norm_mk] }

/-- The canonical linear isometric equivalence between the completion of the separation quotient
of a seminormed space and the completion of the space itself, upgrading
`UniformSpace.Completion.completionSeparationQuotientEquiv`. -/
noncomputable def completionSeparationQuotientₗᵢ :
    Completion (SeparationQuotient E) ≃ₗᵢ[𝕜] Completion E :=
  LinearIsometryEquiv.ofSurjective (liftToComplₗᵢ 𝕜 E).fromCompletion <|
    (liftToComplₗᵢ 𝕜 E).surjective_fromCompletion_of_denseRange <|
      (denseRange_coe).mono <| by
        rintro _ ⟨x, rfl⟩
        exact ⟨SeparationQuotient.mk x, SeparationQuotient.liftCLM_mk _ _ x⟩

variable {𝕜 E}

/-- On classes in `SeparationQuotient E`, `completionSeparationQuotientₗᵢ` sends
`SeparationQuotient.mk x` to `x`. -/
@[simp] theorem completionSeparationQuotientₗᵢ_coe_mk (x : E) :
    completionSeparationQuotientₗᵢ 𝕜 E
      ((SeparationQuotient.mk x : SeparationQuotient E) : Completion (SeparationQuotient E)) =
      (x : Completion E) :=
  ((liftToComplₗᵢ 𝕜 E).fromCompletion_apply_coe _).trans (SeparationQuotient.liftCLM_mk _ _ x)

/-- On `E`, the inverse of `completionSeparationQuotientₗᵢ` sends `x` to
`SeparationQuotient.mk x`. -/
@[simp] theorem completionSeparationQuotientₗᵢ_symm_coe (x : E) :
    (completionSeparationQuotientₗᵢ 𝕜 E).symm (x : Completion E) =
      ((SeparationQuotient.mk x : SeparationQuotient E) : Completion (SeparationQuotient E)) :=
  (completionSeparationQuotientₗᵢ 𝕜 E).injective <| by simp

/-- Underlying equivalence of `completionSeparationQuotientₗᵢ` is
`completionSeparationQuotientEquiv`. -/
@[simp] theorem toEquiv_completionSeparationQuotientₗᵢ :
    (completionSeparationQuotientₗᵢ 𝕜 E).toEquiv = completionSeparationQuotientEquiv E :=
  Equiv.ext fun z ↦ Completion.induction_on z
    (isClosed_eq (completionSeparationQuotientₗᵢ 𝕜 E).continuous
      uniformContinuous_completionSeparationQuotientEquiv.continuous) <|
    SeparationQuotient.surjective_mk.forall.2 fun _ ↦ by
      simp [completionSeparationQuotientEquiv,
        extension_coe (SeparationQuotient.uniformContinuous_lift' _),
        SeparationQuotient.lift'_mk (uniformContinuous_coe E)]

/-- `completionSeparationQuotientₗᵢ` intertwines any uniformly continuous scalar action. -/
@[simp] theorem completionSeparationQuotientₗᵢ_smul {A : Type*} [SMul A E]
    [UniformContinuousConstSMul A E] (a : A) (u : Completion (SeparationQuotient E)) :
    completionSeparationQuotientₗᵢ 𝕜 E (a • u) = a • completionSeparationQuotientₗᵢ 𝕜 E u := by
  let e := completionSeparationQuotientₗᵢ 𝕜 E
  exact Completion.induction_on u
    (isClosed_eq (e.continuous.comp (continuous_const_smul a))
      ((continuous_const_smul a).comp e.continuous)) <|
    SeparationQuotient.surjective_mk.forall.2 fun x ↦ by
      rw [← coe_smul, ← SeparationQuotient.mk_smul, completionSeparationQuotientₗᵢ_coe_mk,
        completionSeparationQuotientₗᵢ_coe_mk, coe_smul]

@[simp] theorem completionSeparationQuotientₗᵢ_symm_smul {A : Type*} [SMul A E]
    [UniformContinuousConstSMul A E] (a : A) (u : Completion E) :
    (completionSeparationQuotientₗᵢ 𝕜 E).symm (a • u) =
      a • (completionSeparationQuotientₗᵢ 𝕜 E).symm u :=
  (completionSeparationQuotientₗᵢ 𝕜 E).injective <| by simp

end UniformSpace.Completion
