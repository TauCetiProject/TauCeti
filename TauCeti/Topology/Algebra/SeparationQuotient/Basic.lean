/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Uniform scalar actions and continuous semilinear lifts on the separation quotient

* `SeparationQuotient.instUniformContinuousConstSMul`: uniformly continuous scalar multiplication
  descends to `SeparationQuotient X`.
* `SeparationQuotient.liftCLM_smul`, `SeparationQuotient.liftCLM_smul_iff`: lifting a continuous
  semilinear map to `SeparationQuotient M` preserves, and reflects, equivariance between auxiliary
  scalar actions.
* `SeparationQuotient.eq_liftCLM_iff`: `SeparationQuotient.liftCLM f hf` is the unique continuous
  semilinear map on `SeparationQuotient M` factoring `f` through `SeparationQuotient.mk`.
-/

public section

namespace SeparationQuotient

/-- Uniformly continuous scalar multiplication descends to the separation quotient. -/
instance instUniformContinuousConstSMul {M X : Type*} [UniformSpace X]
    [SMul M X] [UniformContinuousConstSMul M X] :
    UniformContinuousConstSMul M (SeparationQuotient X) :=
  ⟨fun b ↦ uniformContinuous_dom.2 <| by
    simpa only [Function.comp_def, ← mk_smul] using
      uniformContinuous_mk.comp (uniformContinuous_const_smul b)⟩

variable {R S A B M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [Semiring S] [AddCommMonoid N] [Module S N] [TopologicalSpace N] {σ : R →+* S}

/-- Lifting a continuous semilinear map to `SeparationQuotient M` preserves equivariance between
auxiliary scalar actions. -/
theorem liftCLM_smul [SMul A M] [ContinuousConstSMul A M] [SMul B N]
    (f : M →SL[σ] N) (hf_insep : ∀ x y, Inseparable x y → f x = f y)
    {a : A} {b : B} (hf_smul : ∀ x : M, f (a • x) = b • f x) (z : SeparationQuotient M) :
    liftCLM f hf_insep (a • z) = b • liftCLM f hf_insep z := by
  rcases surjective_mk z with ⟨x, rfl⟩; rw [← mk_smul, liftCLM_mk, liftCLM_mk, hf_smul]

/-- `SeparationQuotient.liftCLM f hf` intertwines an `A`-action with a `B`-action along
`ψ : A → B` if and only if `f` does. -/
theorem liftCLM_smul_iff [SMul A M] [ContinuousConstSMul A M] [SMul B N] (ψ : A → B)
    (f : M →SL[σ] N) (hf_insep : ∀ x y, Inseparable x y → f x = f y) :
    (∀ (a : A) (z : SeparationQuotient M),
        liftCLM f hf_insep (a • z) = ψ a • liftCLM f hf_insep z) ↔
      ∀ (a : A) (x : M), f (a • x) = ψ a • f x :=
  ⟨fun h a x ↦ by simpa only [← mk_smul, liftCLM_mk] using h a (mk x),
    fun h a ↦ liftCLM_smul f hf_insep (h a)⟩

/-- Uniqueness in the universal property of `SeparationQuotient M` for continuous semilinear
maps. -/
theorem eq_liftCLM_iff (f : M →SL[σ] N) (hf_insep : ∀ x y, Inseparable x y → f x = f y)
    (g : SeparationQuotient M →SL[σ] N) :
    g = liftCLM f hf_insep ↔ ∀ x : M, g (mk x) = f x :=
  ⟨fun h x ↦ by rw [h, liftCLM_mk],
    fun h ↦ ContinuousLinearMap.ext <| surjective_mk.forall.2 fun x ↦ by rw [h, liftCLM_mk]⟩

end SeparationQuotient
