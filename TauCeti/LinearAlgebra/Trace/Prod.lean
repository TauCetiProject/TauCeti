/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# Block upper triangular endomorphisms of a product

An endomorphism `F` of `A × C` that preserves the first summand, acting there as `fA`, and covers
`fC` on the second is *block upper triangular*: its only off-diagonal block is the `C → A` map
`fst ∘ F ∘ inr`. This file records that normal form and the resulting trace identity.

## Main results

* `LinearMap.eq_prodMap_add_inl_comp_snd` — the normal form, over an arbitrary semiring.
* `LinearMap.trace_prodMap_add_inl_comp_snd` — the trace of a block upper triangular endomorphism
  is the sum of the traces of its diagonal blocks.

The trace identity needs free finite modules over a commutative ring, since that is what Mathlib's
`LinearMap.trace_prodMap'` and `LinearMap.trace_comp_comm'` require; the normal form itself needs
neither commutativity, finiteness, nor additive inverses.
-/

public section

namespace LinearMap

/-- An endomorphism of `A × C` that preserves the first summand, acting there as `fA`, and covers
`fC` on the second, is block upper triangular: its only off-diagonal block is `C → A`. -/
theorem eq_prodMap_add_inl_comp_snd {R A C : Type*} [Semiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid C] [Module R C]
    {fA : A →ₗ[R] A} {fC : C →ₗ[R] C} (F : (A × C) →ₗ[R] A × C)
    (hinl : F ∘ₗ inl R A C = inl R A C ∘ₗ fA)
    (hsnd : snd R A C ∘ₗ F = fC ∘ₗ snd R A C) :
    F = prodMap fA fC + inl R A C ∘ₗ (fst R A C ∘ₗ F ∘ₗ inr R A C) ∘ₗ snd R A C := by
  have hinl' (a : A) : F (a, 0) = (fA a, 0) := by simpa using congr($hinl a)
  have hsnd' (x : A × C) : (F x).2 = fC x.2 := by simpa using congr($hsnd x)
  ext <;> simp [Prod.mk_zero_zero, hinl', hsnd']

/-- The trace of a block upper triangular endomorphism of `A × C` is the sum of the traces of its
diagonal blocks `fA` and `fC`; the off-diagonal block `u : C → A` does not contribute. -/
theorem trace_prodMap_add_inl_comp_snd {R A C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [Module.Free R A] [Module.Finite R A]
    [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
    (fA : A →ₗ[R] A) (fC : C →ₗ[R] C) (u : C →ₗ[R] A) :
    trace R (A × C) (prodMap fA fC + inl R A C ∘ₗ u ∘ₗ snd R A C)
      = trace R A fA + trace R C fC := by
  -- Cycling the off-diagonal term puts `snd ∘ inl = 0` in the middle.
  rw [map_add, trace_prodMap', trace_comp_comm']
  simp [comp_assoc]

end LinearMap
