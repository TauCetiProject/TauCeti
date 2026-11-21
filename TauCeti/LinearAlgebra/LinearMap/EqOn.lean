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
generator, and when they agree on the span of a family of submodules (`LinearMap.eqOn_iSup_iff`).
In particular, two semilinear maps agreeing on every member of a family of submodules spanning the
source are equal (`LinearMap.ext_of_iSup_eq_top`).
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

include σ in
/-- Two semilinear maps agree on the span of a family of submodules if and only if they agree on
each member of the family. -/
theorem eqOn_iSup_iff {ι : Sort*} {f g : F} {A : ι → Submodule R M} :
    Set.EqOn f g ↑(⨆ i, A i) ↔ ∀ i, Set.EqOn f g (A i) := by
  rw [← LinearMap.coe_ofClass (f := f), ← LinearMap.coe_ofClass (f := g),
    ← LinearMap.le_eqLocus, iSup_le_iff]
  simp only [LinearMap.le_eqLocus]

include σ in
/-- Two semilinear maps that agree on every member of a family of submodules spanning the source
are equal. -/
theorem ext_of_iSup_eq_top {ι : Sort*} {A : ι → Submodule R M} (hA : ⨆ i, A i = ⊤) {f g : F}
    (h : ∀ i, ∀ x ∈ A i, f x = g x) : f = g :=
  DFunLike.ext _ _ fun x ↦ eqOn_iSup_iff.2 h (hA ▸ Submodule.mem_top (x := x))

end LinearMap
