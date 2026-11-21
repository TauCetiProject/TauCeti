/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Topology.Algebra.UniformRing

/-!
# Completion of continuous semilinear maps and equivalences

Subtraction of continuous semilinear maps between uniform modules commutes with extension to the
separated completions (`ContinuousLinearMap.completion_sub`). Extending a continuous semilinear
map to the completion of its domain via `ContinuousLinearMap.fromCompletion` preserves
multiplication (`ContinuousLinearMap.fromCompletion_mul`) and star
(`ContinuousLinearMap.fromCompletion_star`) whenever the map does so on the dense domain.

A continuous semilinear equivalence of uniform additive groups extends to their separated
completions (`ContinuousLinearEquiv.completion`). The construction completes its forward and
inverse continuous semilinear maps using Mathlib's `ContinuousLinearMap.completion`. No separation
or completeness assumption on the original spaces is needed.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

section Completion

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

end Completion

section FromCompletion

variable {R S E F : Type*} [Semiring R] [Semiring S]
  [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [Module R E] [UniformContinuousConstSMul R E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F]
  [Module S F] [UniformContinuousConstSMul S F]
  {σ : R →+* S} [T0Space F] [CompleteSpace F]

/-- Extending a multiplicative continuous semilinear map to the completion preserves
multiplication. -/
theorem fromCompletion_mul [Mul E] [ContinuousMul E] [ContinuousMul (Completion E)]
    [Mul F] [ContinuousMul F] (f : E →SL[σ] F) (hf : ∀ a b : E, f (a * b) = f a * f b)
    (x y : Completion E) :
    f.fromCompletion (x * y) = f.fromCompletion x * f.fromCompletion y := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a b => simp only [← Completion.coe_mul', fromCompletion_apply_coe, hf]

/-- Extending a star-preserving continuous semilinear map to the completion preserves `star`. -/
theorem fromCompletion_star [StarAddMonoid E] [ContinuousStar E] [Star F] [ContinuousStar F]
    (f : E →SL[σ] F) (hf : ∀ a : E, f (star a) = star (f a)) (x : Completion E) :
    f.fromCompletion (star x) = star (f.fromCompletion x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a => simp only [← Completion.coe_star, fromCompletion_apply_coe, hf]

end FromCompletion

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
