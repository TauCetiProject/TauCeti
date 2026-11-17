/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.SeparationQuotient.Basic

/-!
# Universal properties of `SeparationQuotient` for continuous semilinear maps

Characterizes `SeparationQuotient.liftCLM f hf : SeparationQuotient M →SL[σ] N` for a `T₀` codomain
`N` and its equivariance along an auxiliary scalar action.

## Main declarations

* `SeparationQuotient.liftCLM_smul_iff`: `liftCLM f hf` intertwines scalar actions iff `f` does.
* `SeparationQuotient.comp_mkCLM_eq_iff`: `g ∘ mkCLM R M = f ↔ g = liftCLM f _` for `T₀` `N`.
-/

public section

namespace SeparationQuotient

variable {R S M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [Semiring S] [AddCommMonoid N] [Module S N] [TopologicalSpace N] {σ : R →+* S}

/-- The lift `liftCLM f hf : SeparationQuotient M →SL[σ] N` intertwines an `A₀`-action with a
`B`-action along `ψ : A₀ → B` if and only if `f` does. -/
theorem liftCLM_smul_iff {A₀ B : Type*} [SMul A₀ M] [ContinuousConstSMul A₀ M] [SMul B N]
    (ψ : A₀ → B) (f : M →SL[σ] N) (hf : ∀ x y : M, Inseparable x y → f x = f y) :
    (∀ (a₀ : A₀) (q : SeparationQuotient M), liftCLM f hf (a₀ • q) = ψ a₀ • liftCLM f hf q) ↔
      ∀ (a₀ : A₀) (x : M), f (a₀ • x) = ψ a₀ • f x :=
  ⟨fun h a₀ x ↦ by simpa only [← mk_smul, liftCLM_mk] using h a₀ (mk x),
    fun h a₀ ↦ surjective_mk.forall.2 fun x ↦ by simpa only [← mk_smul, liftCLM_mk] using h a₀ x⟩

/-- Universal property of `SeparationQuotient M` for continuous semilinear maps into a `T₀`
topological module `N`: `g ∘ mkCLM R M = f` if and only if `g = liftCLM f _`. -/
theorem comp_mkCLM_eq_iff [T0Space N] (f : M →SL[σ] N) (g : SeparationQuotient M →SL[σ] N) :
    g.comp (mkCLM R M) = f ↔ g = liftCLM f fun _ _ h ↦ (h.map f.continuous).eq :=
  ⟨fun h ↦ ContinuousLinearMap.ext <| surjective_mk.forall.2 fun x ↦ by simp [← h],
    fun h ↦ by ext x; simp [h]⟩

end SeparationQuotient
