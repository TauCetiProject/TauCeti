/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spans over a second ring of scalars

An isomorphism of a larger-scalar span transports the original submodule to a submodule
generating its target. When a scalar `r` takes one coefficient subalgebra into another,
the same scalar takes the enlarged span back into the original submodule. These two facts
let one control lattices over a smaller order from their spans over an overorder.
-/

public section

open Pointwise

namespace Submodule

/-- An isomorphism from the larger-scalar span of a submodule to `N` carries the
original submodule to an isomorphic submodule spanning `N`. -/
theorem exists_span_eq_and_nonempty_linearEquiv {R S V W : Type*} [Semiring R] [Semiring S]
    [SMul R S] [AddCommMonoid V] [Module R V] [Module S V] [IsScalarTower R S V]
    [AddCommMonoid W] [Module R W] [Module S W] [IsScalarTower R S W]
    (M : Submodule R V) {N : Submodule S W} (e : span S (M : Set V) ≃ₗ[S] N) :
    ∃ P : Submodule R W, span S (P : Set W) = N ∧ Nonempty (M ≃ₗ[R] P) := by
  let g := N.subtype ∘ₗ e.toLinearMap
  let f := g.restrictScalars R ∘ₗ M.inclusionSpan S
  refine ⟨LinearMap.range f, ?_, ⟨LinearEquiv.ofInjective f
    (N.injective_subtype.comp (e.injective.comp (M.injective_inclusionSpan S)))⟩⟩
  calc
    span S (f.range : Set W) = (span S (Set.range (M.inclusionSpan S))).map g := by
      simp only [f, LinearMap.coe_range, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Set.range_comp, map_span]
    _ = N := by simp [M.span_range_inclusionSpan S, g, LinearMap.range_comp]

/-- If `r Γ ⊆ Λ`, multiplication by `r` takes the `Γ`-span of a `Λ`-module back into it. -/
theorem smul_restrictScalars_span_le {R A V : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid V] [Module A V] [Module R V] [IsScalarTower R A V]
    {Λ Γ : Subalgebra R A} (M : Submodule Λ V) {r : R}
    (hr : ∀ a ∈ Γ, r • a ∈ Λ) :
    r • (span Γ (M : Set V)).restrictScalars R ≤ M.restrictScalars R := by
  intro y hy
  rw [mem_smul_pointwise_iff_exists] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simp only [restrictScalars_mem] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => simp
  | add x y _ _ hx hy => simpa only [smul_add] using M.add_mem hx hy
  | smul_mem a x hx =>
    simpa only [Subalgebra.smul_def, smul_assoc] using
      M.smul_mem (⟨r • (a : A), hr a a.property⟩ : Λ) hx

end Submodule
