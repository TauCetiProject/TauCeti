/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Completion of continuous semilinear maps and equivalences

A continuous semilinear equivalence of uniform additive groups extends to their separated
completions. The construction completes its forward and inverse continuous semilinear maps
using Mathlib's `ContinuousLinearMap.completion`. No separation or completeness assumption on
the original spaces is needed.

This file also records the universal property of `ContinuousLinearMap.fromCompletion` via
`UniformSpace.Completion.toComplL` and equivariance criteria for `fromCompletion` and `completion`
with respect to auxiliary scalar actions.

## Main declarations

* `ContinuousLinearEquiv.completion`: extension of a continuous semilinear equivalence to
  separated completions.
* `ContinuousLinearMap.fromCompletion_smul_iff`: `f.fromCompletion` intertwines a scalar action
  along `ψ : A₀ → B` if and only if `f` does.
* `ContinuousLinearMap.completion_smul`, `ContinuousLinearMap.completion_smul_iff`: equivariance
  of `f.completion` along `ψ : A₀ → B`.
* `ContinuousLinearMap.comp_toComplL_eq_iff`: universal property
  `g ∘ toComplL = f ↔ g = f.fromCompletion`.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

variable {α β : Type*} {R S : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]
  [Semiring S] [Module S α] [UniformContinuousConstSMul S α]
  [Semiring R] [UniformSpace β] [AddCommGroup β] [IsUniformAddGroup β]
  [Module R β] [UniformContinuousConstSMul R β] {σ : S →+* R}

/-- `f.fromCompletion : Completion α →SL[σ] β` intertwines an `A₀`-action with a `B`-action along
`ψ : A₀ → B` if and only if `f` does on `α`. -/
theorem fromCompletion_smul_iff [T0Space β] [CompleteSpace β]
    {A₀ B : Type*} [SMul A₀ α] [UniformContinuousConstSMul A₀ α]
    [SMul B β] [ContinuousConstSMul B β] (ψ : A₀ → B) (f : α →SL[σ] β) :
    (∀ (a₀ : A₀) (x : Completion α),
        f.fromCompletion (a₀ • x) = ψ a₀ • f.fromCompletion x) ↔
      ∀ (a₀ : A₀) (x : α), f (a₀ • x) = ψ a₀ • f x := by
  refine ⟨fun h a₀ x ↦ by
      simpa only [← Completion.coe_smul, fromCompletion_apply_coe] using h a₀ x,
    fun h a₀ x ↦ Completion.induction_on x
      (isClosed_eq (f.fromCompletion.continuous.comp (continuous_const_smul a₀))
        ((continuous_const_smul (ψ a₀)).comp f.fromCompletion.continuous))
      fun u ↦ by simp [← Completion.coe_smul, h a₀ u]⟩

/-- If `f : α →SL[σ] β` intertwines an `A₀`-action with a `B`-action along `ψ : A₀ → B`, then so
does `f.completion : Completion α →SL[σ] Completion β`. -/
theorem completion_smul {A₀ B : Type*} [SMul A₀ α] [UniformContinuousConstSMul A₀ α]
    [SMul B β] [UniformContinuousConstSMul B β] (ψ : A₀ → B) (f : α →SL[σ] β)
    (hf : ∀ (a₀ : A₀) (x : α), f (a₀ • x) = ψ a₀ • f x) (a₀ : A₀) (x : Completion α) :
    f.completion (a₀ • x) = ψ a₀ • f.completion x :=
  Completion.induction_on x
    (isClosed_eq (f.completion.continuous.comp (continuous_const_smul a₀))
      ((continuous_const_smul (ψ a₀)).comp f.completion.continuous))
    fun u ↦ by simp [← Completion.coe_smul, hf a₀ u]

/-- When `β` is `T₀`, `f.completion : Completion α →SL[σ] Completion β` intertwines an `A₀`-action
with a `B`-action along `ψ : A₀ → B` if and only if `f` does on `α`. -/
theorem completion_smul_iff [T0Space β] {A₀ B : Type*} [SMul A₀ α]
    [UniformContinuousConstSMul A₀ α] [SMul B β] [UniformContinuousConstSMul B β]
    (ψ : A₀ → B) (f : α →SL[σ] β) :
    (∀ (a₀ : A₀) (x : Completion α), f.completion (a₀ • x) = ψ a₀ • f.completion x) ↔
      ∀ (a₀ : A₀) (x : α), f (a₀ • x) = ψ a₀ • f x := by
  refine ⟨fun h a₀ x ↦ ?_, completion_smul ψ f⟩
  have hcoe := h a₀ (x : Completion α)
  rwa [← Completion.coe_smul, completion_apply_coe, completion_apply_coe,
    ← Completion.coe_smul, Completion.coe_inj] at hcoe

/-- Universal property of `Completion α` for continuous semilinear maps into a complete `T₀`
uniform module `β`: `g : Completion α →SL[σ] β` factors `f : α →SL[σ] β` through
`Completion.toComplL` if and only if `g = f.fromCompletion`. -/
theorem comp_toComplL_eq_iff [T0Space β] [CompleteSpace β]
    (f : α →SL[σ] β) (g : Completion α →SL[σ] β) :
    g.comp (Completion.toComplL (S := S)) = f ↔ g = f.fromCompletion :=
  ⟨fun h ↦ (f.fromCompletion_unique g fun u ↦ (DFunLike.congr_fun h u).symm).symm,
    fun h ↦ by ext x; simp [h]⟩

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
