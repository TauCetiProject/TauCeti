/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The left kernel of a singular matrix over a finite field

A square matrix `Z` over a field with `q` elements and `det Z = 0` has a nonzero vector `y` with
`y ᵥ* Z = 0` (Mathlib's `Matrix.exists_vecMul_eq_zero_iff`), and then all `q` multiples of `y`
lie in the left kernel. So the left kernel has at least `q` elements.

## Main results

* `Matrix.card_le_card_filter_vecMul_eq_zero`: `q ≤ #{y | y ᵥ* Z = 0}` when `det Z = 0`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC), file `src/New/Spanning/SecondMoment/PositiveType.lean`,
declaration `New.card_le_card_filter_vecMul_eq_zero`.
-/

public section

open Finset

namespace Matrix

variable {k m : Type*} [Field k] [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m]

/-- A singular square matrix over a field with `q` elements has at least `q` vectors in its left
kernel. -/
theorem card_le_card_filter_vecMul_eq_zero {Z : Matrix m m k} (hZ : Z.det = 0) :
    Fintype.card k ≤ #{y : m → k | y ᵥ* Z = 0} := by
  -- The left kernel holds the `q` multiples of some `y ≠ 0`.
  obtain ⟨y, hy, hyZ⟩ : ∃ y : m → k, y ≠ 0 ∧ y ᵥ* Z = 0 := exists_vecMul_eq_zero_iff.2 hZ
  exact card_le_card_of_injOn (fun t : k ↦ t • y) (by simp [smul_vecMul, hyZ])
    (smul_left_injective k hy).injOn

end Matrix
