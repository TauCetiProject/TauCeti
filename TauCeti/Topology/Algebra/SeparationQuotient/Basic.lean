/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.SeparationQuotient.Basic

/-!
# Continuous semilinear lifts to the separation quotient

Equivariance and uniqueness for `SeparationQuotient.liftCLM`:

* `SeparationQuotient.liftCLM_smul`: lifting a continuous semilinear map to `SeparationQuotient M`
  preserves equivariance for an auxiliary continuous scalar action.
* `SeparationQuotient.eq_liftCLM_iff`: `SeparationQuotient.liftCLM f hf` is the unique continuous
  semilinear map on `SeparationQuotient M` factoring `f` through `SeparationQuotient.mk`.
-/

public section

namespace SeparationQuotient

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

end SeparationQuotient
