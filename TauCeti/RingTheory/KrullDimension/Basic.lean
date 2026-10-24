/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Rings of finite Krull dimension

A ring whose Krull dimension is a natural number has finite Krull dimension. This is the form in
which finiteness of the dimension usually arises, from a computation `dim R = n`.

A surjection from a domain of finite Krull dimension onto a ring of at least the same dimension is
injective, since a nonzero kernel element would be a nonzerodivisor and so would lower the
dimension.

## Main results

* `FiniteRingKrullDim.of_ringKrullDim_eq_natCast`: a ring of Krull dimension `n : ℕ` has finite
  Krull dimension.
* `RingHom.injective_of_surjective_of_ringKrullDim_le`: a surjection from a domain of finite
  Krull dimension onto a ring of at least the same dimension is injective.
-/

public section

/-- A ring whose Krull dimension is a natural number `n` has finite Krull dimension. -/
theorem FiniteRingKrullDim.of_ringKrullDim_eq_natCast {R : Type*} [CommRing R] {n : ℕ}
    (h : ringKrullDim R = n) : FiniteRingKrullDim R :=
  finiteRingKrullDim_iff_ne_bot_and_top.mpr
    (h ▸ ⟨WithBot.natCast_ne_bot _, WithBot.coe_inj.not.mpr (ENat.natCast_ne_top _)⟩)

/-- A surjective ring homomorphism from a domain of finite Krull dimension onto a ring of at least
the same dimension is injective. -/
theorem RingHom.injective_of_surjective_of_ringKrullDim_le {R S : Type*} [CommRing R]
    [IsDomain R] [FiniteRingKrullDim R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (hdim : ringKrullDim R ≤ ringKrullDim S) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun r hr ↦ by_contra fun hr0 ↦ ?_
  -- A nonzero kernel element is a nonzerodivisor, so it would lower the dimension.
  have hlt := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_of_ne_zero hr0) hr
  rw [le_antisymm (ringKrullDim_le_of_surjective f hf) hdim] at hlt
  have htop := ringKrullDim_ne_top (R := R)
  lift ringKrullDim R to ℕ∞ using ringKrullDim_ne_bot with d
  lift d to ℕ using by simpa using htop
  norm_cast at hlt
  omega
