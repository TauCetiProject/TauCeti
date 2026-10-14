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
simpler subquotients without requiring the ambient module to be flat.

## Main results

* `Function.Exact.flat_of_injective_of_surjective`: the middle term of a short exact sequence
  with flat outer terms is flat.
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
