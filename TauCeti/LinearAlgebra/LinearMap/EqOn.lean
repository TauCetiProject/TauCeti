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

This file characterizes when two semilinear maps agree on a submodule enlarged by one additional
generator, and shows that two semilinear maps agreeing on every member of a family of submodules
spanning the source are equal (`LinearMap.ext_of_iSup_eq_top`).
-/

public section

namespace LinearMap

universe u₁ u₂ u₃ u₄ u₅

variable {R : Type u₁} {R₂ : Type u₂} {M : Type u₃} {M₂ : Type u₄} {F : Type u₅}
  [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
  [Module R M] [Module R₂ M₂] {σ : R →+* R₂} [FunLike F M M₂] [SemilinearMapClass F σ M M₂]

include σ in
/-- Two semilinear maps agree on `W ⊔ R ∙ x` if and only if they agree on `W` and at `x`. -/
theorem eqOn_sup_span_singleton_iff {f g : F} {W : Submodule R M} {x : M} :
    Set.EqOn f g ↑(W ⊔ Submodule.span R {x}) ↔ Set.EqOn f g W ∧ f x = g x := by
  rw [← LinearMap.coe_ofClass (f := f), ← LinearMap.coe_ofClass (f := g),
    ← LinearMap.le_eqLocus, ← LinearMap.le_eqLocus, sup_le_iff,
    Submodule.span_singleton_le_iff_mem, LinearMap.mem_eqLocus]

/-- Two semilinear maps that agree on every member of a family of submodules spanning the source
are equal. -/
theorem ext_of_iSup_eq_top {R R₂ ι M M₂ : Type*} [Semiring R] [Semiring R₂]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂] {σ : R →+* R₂}
    {A : ι → Submodule R M} (hA : ⨆ i, A i = ⊤) {f g : M →ₛₗ[σ] M₂}
    (h : ∀ i, ∀ x ∈ A i, f x = g x) : f = g :=
  ext_on (s := ⋃ i, (A i : Set M)) (by rw [← Submodule.iSup_eq_span, hA])
    fun x hx ↦ by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact h i x hi

end LinearMap
