/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Pointwise equality on generated submodules

This file provides a small extension principle for semilinear maps that agree on a submodule and
on one additional generator.
-/

public section

namespace TauCeti.LinearMap

universe u₁ u₂ u₃ u₄

variable {R : Type u₁} {R₂ : Type u₂} {M : Type u₃} {M₂ : Type u₄}
  [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
  [Module R M] [Module R₂ M₂] {σ : R →+* R₂}

/-- Two semilinear maps that agree on `W` and at `x` agree on `W ⊔ R ∙ x`. -/
theorem eqOn_sup_span_singleton {f g : M →ₛₗ[σ] M₂} {W : Submodule R M} {x : M}
    (hW : Set.EqOn f g W) (hx : f x = g x) :
    Set.EqOn f g (↑(W ⊔ Submodule.span R {x}) : Set M) := by
  apply _root_.LinearMap.eqOn_sup hW
  apply _root_.LinearMap.eqOn_span'
  intro y hy
  simpa only [Set.mem_singleton_iff] using hy ▸ hx

end TauCeti.LinearMap
