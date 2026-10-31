/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Elementary linear-equivalence transport

Transport of submodule stability through an intertwining linear equivalence.
Symmetry of a linear automorphism agrees with inversion in its group structure.
A linear equivalence carries generators to generators, so over a commutative ring whose only unit
is `1`, such as `ZMod 2`, a module linearly equivalent to the ring has a single generator.
-/

public section

namespace LinearEquiv

/-- Symmetry of a linear automorphism is its group inverse. -/
theorem symm_eq_inv {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (e : V ≃ₗ[R] V) : e.symm = e⁻¹ := rfl

/-- Transport stability of a mapped submodule through an intertwining linear equivalence. -/
theorem mem_of_preserves_map
    {R V W : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (e : V ≃ₗ[R] W) (p : Submodule R V) (q : Submodule R W)
    (hmap : p.map e.toLinearMap = q) (f : V → V) (g : W → W)
    (hcomm : ∀ x, e (f x) = g (e x))
    (hstable : ∀ {y}, y ∈ q → g y ∈ q)
    {x : V} (hx : x ∈ p) : f x ∈ p := by
  have hex : e x ∈ q := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hx
  have hfx := hstable hex
  rw [← hcomm x, ← hmap] at hfx
  simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hfx

/-- A linear equivalence carries generators to generators: `e x` spans the codomain if and only if
`x` spans the domain. -/
theorem span_singleton_apply_eq_top_iff {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) {x : M} :
    Submodule.span R {e x} = ⊤ ↔ Submodule.span R {x} = ⊤ := by
  rw [← Set.image_singleton, Submodule.span_image_linearEquiv, Submodule.map_eq_top_iff]

/-- **Uniqueness of generators**: over a commutative ring `K` whose only unit is `1`, such as
`ZMod 2`, a module linearly equivalent to `K` has a single generator, since its generators
correspond to the units of `K`. -/
theorem eq_of_span_singleton_eq_top {K N : Type*} [CommSemiring K] [Subsingleton Kˣ]
    [AddCommMonoid N] [Module K N] (φ : N ≃ₗ[K] K) {x y : N}
    (hx : Submodule.span K {x} = ⊤) (hy : Submodule.span K {y} = ⊤) : x = y := by
  have hx' := Ideal.span_singleton_eq_top.1 (φ.span_singleton_apply_eq_top_iff.2 hx)
  have hy' := Ideal.span_singleton_eq_top.1 (φ.span_singleton_apply_eq_top_iff.2 hy)
  exact φ.injective (congrArg Units.val (Subsingleton.elim hx'.unit hy'.unit))

end LinearEquiv
