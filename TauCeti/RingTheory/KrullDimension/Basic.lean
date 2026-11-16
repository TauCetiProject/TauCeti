/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Rings of finite Krull dimension

A semiring whose Krull dimension is a natural number has finite Krull dimension. This is the form in
which finiteness of the dimension usually arises, from a computation `dim R = n`.

A surjection from a domain of finite Krull dimension is injective exactly when its target has at
least the same dimension: a nonzero kernel element would be a nonzerodivisor and so would lower the
dimension, while an injective surjection is an isomorphism.

## Main results

* `FiniteRingKrullDim.of_ringKrullDim_eq_natCast`: a semiring of Krull dimension `n : ℕ` has
  finite Krull dimension.
* `RingHom.injective_iff_ringKrullDim_le_of_surjective`: a surjection from a domain of finite
  Krull dimension is injective if and only if its target has at least the same dimension.
-/

public section

/-- A semiring whose Krull dimension is a natural number `n` has finite Krull dimension. -/
theorem FiniteRingKrullDim.of_ringKrullDim_eq_natCast {R : Type*} [CommSemiring R] {n : ℕ}
    (h : ringKrullDim R = n) : FiniteRingKrullDim R :=
  finiteRingKrullDim_iff_ne_bot_and_top.mpr
    (h ▸ ⟨WithBot.natCast_ne_bot _, WithBot.coe_inj.not.mpr (ENat.natCast_ne_top _)⟩)

/-- A surjective ring homomorphism from a domain of finite Krull dimension is injective if and
only if its target has at least the same dimension. -/
theorem RingHom.injective_iff_ringKrullDim_le_of_surjective {R S : Type*} [CommRing R]
    [IsDomain R] [FiniteRingKrullDim R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective f ↔ ringKrullDim R ≤ ringKrullDim S := by
  refine ⟨fun hinj ↦ ?_, fun hdim ↦ ?_⟩
  · -- An injective surjection is an isomorphism, so it preserves the dimension.
    exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective f ⟨hinj, hf⟩)).le
  refine (injective_iff_map_eq_zero f).2 fun r hr ↦ by_contra fun hr0 ↦ ?_
  -- A nonzero kernel element is a nonzerodivisor, so it would lower the dimension.
  have hlt := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero hr0) hr
  -- Write the finite dimension of `R` as a natural number `d`, so that `dim S < d ≤ dim S`.
  lift ringKrullDim R to ℕ∞ using ringKrullDim_ne_bot with d hd
  lift d to ℕ using by simpa [← hd] using ringKrullDim_ne_top (R := R)
  exact (ENat.WithBot.add_one_le_natCast_iff.mp hlt).not_ge hdim
