/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.Fintype.Card

/-!
# Averaging a constant over a finite type

When the cardinality of a finite type `G` is invertible in a semiring `𝕜`, the average
`⅟(#G) • ∑ g : G, f g` of a family of vectors in a `𝕜`-module is the normalisation used by
`Representation.averageMap` and by nonlinear averaging operators such as the Bochner average.
This file records that averaging a constant family returns the constant.
-/

public section

namespace TauCeti

/-- Averaging a constant over a finite type `G`, with `#G` invertible in `𝕜`, returns it. -/
theorem invOf_card_smul_sum_const {𝕜 G M : Type*} [Semiring 𝕜] [Fintype G]
    [Invertible (Fintype.card G : 𝕜)] [AddCommMonoid M] [Module 𝕜 M] (v : M) :
    ⅟(Fintype.card G : 𝕜) • ∑ _g : G, v = v := by
  rw [invOf_smul_eq_iff]
  simp [Nat.cast_smul_eq_nsmul]

end TauCeti
