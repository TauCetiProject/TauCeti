/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.FiveLemma

/-!
# Extensions of flat modules

In a short exact sequence `0 → M → N → P → 0` of modules over a commutative ring, if `M` and
`P` are flat, then `N` is flat. This allows flatness of a quotient to be established from
simpler subquotients without requiring the ambient module to be flat. Likewise, if `N` and `P`
are flat, then so is `M`: a submodule of a flat module with flat quotient is flat.

## Main results

* `Function.Exact.flat_of_injective_of_surjective`: the middle term of a short exact sequence
  with flat outer terms is flat.
* `Function.Exact.flat_left_of_injective_of_surjective`: the first term of a short exact
  sequence whose other two terms are flat is flat.
-/

public section

open TensorProduct

universe u v w x

variable {R : Type u} {M : Type v} {N : Type w} {P : Type x} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- The middle term of a short exact sequence with flat outer terms is flat. -/
theorem Function.Exact.flat_of_injective_of_surjective
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    [Module.Flat R M] [Module.Flat R P] : Module.Flat R N := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro A B _ _ _ _ i hi
  -- Tensor the short exact sequence with `A` and `B`, and apply the injective four lemma.
  exact LinearMap.injective_of_surjective_of_injective_of_injective
    (0 : Unit →ₗ[R] A ⊗[R] M) (f.lTensor A) (g.lTensor A)
    (0 : Unit →ₗ[R] B ⊗[R] M) (f.lTensor B) (g.lTensor B)
    (0 : Unit →ₗ[R] Unit) (i.rTensor M) (i.rTensor N) (i.rTensor P)
    (by simp) (by simp) (by simp)
    ((LinearMap.exact_zero_iff_injective Unit _).mpr
      (LinearMap.lTensor_injective_of_exact_of_flat g hg f hf h A))
    (lTensor_exact A h hg)
    ((LinearMap.exact_zero_iff_injective Unit _).mpr
      (LinearMap.lTensor_injective_of_exact_of_flat g hg f hf h B))
    (Function.surjective_to_subsingleton _)
    (Module.Flat.rTensor_preserves_injective_linearMap i hi)
    (Module.Flat.rTensor_preserves_injective_linearMap i hi)

/-- The first term of a short exact sequence whose middle and last terms are flat is flat. -/
theorem Function.Exact.flat_left_of_injective_of_surjective
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    [Module.Flat R N] [Module.Flat R P] : Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro A B _ _ _ _ i hi
  -- `f ⊗ B ∘ i ⊗ M = i ⊗ N ∘ f ⊗ A`, and the right-hand side is injective since `P` and `N`
  -- are flat.
  refine Function.Injective.of_comp (f := f.lTensor B) ?_
  rw [← LinearMap.coe_comp, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap i hi).comp
    (LinearMap.lTensor_injective_of_exact_of_flat g hg f hf h A)
