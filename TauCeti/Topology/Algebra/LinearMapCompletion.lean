/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Completions of continuous semilinear maps and equivalences

A continuous semilinear map between uniform additive groups extends to completions (`completion`
and `fromCompletion`), preserving equivariance for any auxiliary uniformly continuous scalar
actions (`ContinuousLinearMap.completion_smul` and `ContinuousLinearMap.fromCompletion_smul`),
and reflecting it (`completion_smul_iff`, `fromCompletion_smul_iff`). `fromCompletion` is
characterized by `ContinuousLinearMap.comp_toComplL_eq_iff`.
Subtraction of continuous semilinear maps between uniform modules commutes with extension to the
separated completions (`ContinuousLinearMap.completion_sub`).

A continuous semilinear equivalence of uniform additive groups extends to their separated
completions (`ContinuousLinearEquiv.completion`) by completing its forward and inverse continuous
semilinear maps using Mathlib's `ContinuousLinearMap.completion`. No separation or completeness
assumption on the original spaces is needed.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

section Sub

variable {R S E F : Type*} [Ring R] [Ring S]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F]
  [Module R E] [UniformContinuousConstSMul R E]
  [Module S F] [UniformContinuousConstSMul S F]
  {σ : R →+* S}

/-- Completing a difference of continuous semilinear maps is the difference of their
completions. -/
@[simp]
theorem completion_sub (f g : E →SL[σ] F) : (f - g).completion = f.completion - g.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (f - g).completion.continuous (f.completion - g.completion).continuous
  | ih x => simp [← Completion.coe_sub]

end Sub

section SMul

variable {R S A B α β : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring S] [Module S α] [UniformContinuousConstSMul S α]
  [Semiring R] [UniformSpace β] [AddCommGroup β] [IsUniformAddGroup β]
  [Module R β] [UniformContinuousConstSMul R β] {σ : S →+* R}

/-- Extending a continuous semilinear map to completions preserves equivariance between auxiliary
uniformly continuous scalar actions. -/
theorem completion_smul [SMul A α] [UniformContinuousConstSMul A α]
    [SMul B β] [UniformContinuousConstSMul B β]
    (f : α →SL[σ] β) {a : A} {b : B} (hf : ∀ x : α, f (a • x) = b • f x) (z : Completion α) :
    f.completion (a • z) = b • f.completion z :=
  Completion.induction_on z
    (isClosed_eq (f.completion.continuous.comp (continuous_const_smul a))
      ((continuous_const_smul b).comp f.completion.continuous))
    fun x ↦ by rw [← Completion.coe_smul, completion_apply_coe, hf, Completion.coe_smul,
      completion_apply_coe]

/-- Extending a continuous semilinear map into a complete Hausdorff group from the completion of its
domain preserves equivariance between auxiliary scalar actions. -/
theorem fromCompletion_smul [T0Space β] [CompleteSpace β]
    [SMul A α] [UniformContinuousConstSMul A α] [SMul B β] [ContinuousConstSMul B β]
    (f : α →SL[σ] β) {a : A} {b : B} (hf : ∀ x : α, f (a • x) = b • f x) (z : Completion α) :
    f.fromCompletion (a • z) = b • f.fromCompletion z :=
  Completion.induction_on z
    (isClosed_eq (f.fromCompletion.continuous.comp (continuous_const_smul a))
      ((continuous_const_smul b).comp f.fromCompletion.continuous))
    fun x ↦ by rw [← Completion.coe_smul, fromCompletion_apply_coe, hf, fromCompletion_apply_coe]

/-- For a separated codomain `β`, `f.completion` intertwines an `A`-action with a `B`-action along
`ψ : A → B` if and only if `f` does. -/
theorem completion_smul_iff [T0Space β] [SMul A α] [UniformContinuousConstSMul A α]
    [SMul B β] [UniformContinuousConstSMul B β] (ψ : A → B) (f : α →SL[σ] β) :
    (∀ (a : A) (z : Completion α), f.completion (a • z) = ψ a • f.completion z) ↔
      ∀ (a : A) (x : α), f (a • x) = ψ a • f x :=
  ⟨fun h a x ↦ Completion.coe_injective β <| by
      rw [Completion.coe_smul, ← completion_apply_coe, ← completion_apply_coe, ← h,
        Completion.coe_smul],
    fun h a ↦ f.completion_smul (h a)⟩

/-- `f.fromCompletion` intertwines an `A`-action with a `B`-action along `ψ : A → B` if and only if
`f` does. -/
theorem fromCompletion_smul_iff [T0Space β] [CompleteSpace β]
    [SMul A α] [UniformContinuousConstSMul A α] [SMul B β] [ContinuousConstSMul B β]
    (ψ : A → B) (f : α →SL[σ] β) :
    (∀ (a : A) (z : Completion α), f.fromCompletion (a • z) = ψ a • f.fromCompletion z) ↔
      ∀ (a : A) (x : α), f (a • x) = ψ a • f x :=
  ⟨fun h a x ↦ by simpa only [← Completion.coe_smul, fromCompletion_apply_coe] using h a x,
    fun h a ↦ f.fromCompletion_smul (h a)⟩

/-- Universal property of `Completion α` for continuous semilinear maps into a complete separated
module `β`: `g ∘ toComplL = f` if and only if `g = f.fromCompletion`. -/
theorem comp_toComplL_eq_iff [T0Space β] [CompleteSpace β]
    (f : α →SL[σ] β) (g : Completion α →SL[σ] β) :
    g.comp (Completion.toComplL (S := S)) = f ↔ g = f.fromCompletion :=
  ⟨fun h ↦ (f.fromCompletion_unique g fun x ↦ (DFunLike.congr_fun h x).symm).symm,
    fun h ↦ by ext x; simp [h]⟩

end SMul

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {R S E F : Type*} [Semiring R] [Semiring S]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F]
  [Module R E] [UniformContinuousConstSMul R E]
  [Module S F] [UniformContinuousConstSMul S F]
  {σ : R →+* S} {τ : S →+* R} [RingHomInvPair σ τ] [RingHomInvPair τ σ]

/-- Extend a continuous semilinear equivalence to the separated completions. -/
noncomputable def completion (e : E ≃SL[σ] F) : Completion E ≃SL[σ] Completion F := by
  let f := e.toContinuousLinearMap.completion
  let g := e.symm.toContinuousLinearMap.completion
  refine ContinuousLinearEquiv.ofContinuousLinearMap f g ?_ ?_
  · exact ContinuousLinearMap.ext (congr_fun (Completion.ext (f.continuous.comp g.continuous)
      continuous_id (fun x => by simp [f, g])))
  · exact ContinuousLinearMap.ext (congr_fun (Completion.ext (g.continuous.comp f.continuous)
      continuous_id (fun x => by simp [f, g])))

/-- On the original space, the completed equivalence agrees with the original equivalence. -/
@[simp]
theorem completion_apply_coe (e : E ≃SL[σ] F) (x : E) : e.completion x = e x :=
  e.toContinuousLinearMap.completion_apply_coe x

/-- Completing an equivalence commutes with taking its inverse. -/
@[simp]
theorem completion_symm (e : E ≃SL[σ] F) : e.completion.symm = e.symm.completion := by
  rfl

end ContinuousLinearEquiv
