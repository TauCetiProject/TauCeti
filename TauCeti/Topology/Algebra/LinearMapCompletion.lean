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
action (`ContinuousLinearMap.completion_smul` and `ContinuousLinearMap.fromCompletion_smul`).

A continuous semilinear equivalence of uniform additive groups extends to their separated
completions (`ContinuousLinearEquiv.completion`) by completing its forward and inverse continuous
semilinear maps using Mathlib's `ContinuousLinearMap.completion`. No separation or completeness
assumption on the original spaces is needed.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

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
  refine ContinuousLinearEquiv.equivOfInverse f g ?_ ?_
  · exact congr_fun (Completion.ext (g.continuous.comp f.continuous) continuous_id
      (fun x => by simp [f, g]))
  · exact congr_fun (Completion.ext (f.continuous.comp g.continuous) continuous_id
      (fun x => by simp [f, g]))

/-- On the original space, the completed equivalence agrees with the original equivalence. -/
@[simp]
theorem completion_apply_coe (e : E ≃SL[σ] F) (x : E) : e.completion x = e x :=
  e.toContinuousLinearMap.completion_apply_coe x

/-- Completing an equivalence commutes with taking its inverse. -/
@[simp]
theorem completion_symm (e : E ≃SL[σ] F) : e.completion.symm = e.symm.completion := by
  rfl

end ContinuousLinearEquiv
