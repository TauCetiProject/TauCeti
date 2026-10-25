/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Rings of finite Krull dimension

A ring whose Krull dimension is a natural number has finite Krull dimension. This is the form in
which finiteness of the dimension usually arises, from a computation `dim R = n`.

## Main results

* `FiniteRingKrullDim.of_ringKrullDim_eq_natCast`: a ring of Krull dimension `n : ℕ` has finite
  Krull dimension.
-/

public section

/-- A ring whose Krull dimension is a natural number `n` has finite Krull dimension. -/
theorem FiniteRingKrullDim.of_ringKrullDim_eq_natCast {R : Type*} [CommRing R] {n : ℕ}
    (h : ringKrullDim R = n) : FiniteRingKrullDim R :=
  finiteRingKrullDim_iff_ne_bot_and_top.mpr
    (h ▸ ⟨WithBot.natCast_ne_bot _, WithBot.coe_inj.not.mpr (ENat.natCast_ne_top _)⟩)
