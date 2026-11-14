/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.Jordan.Peirce
public import TauCeti.Algebra.AlbertAlgebra.Basic

/-!
# Peirce spaces of the split Albert diagonal frame

This module packages diagonal idempotents and off-diagonal slots into `Jordan.peirceSpace`
for eigenvalues `1`, `0` and `⅟2`. This connects the coordinate multiplication formulas in
`AlbertAlgebra.Basic` to the general Jordan Peirce decomposition and product API once a Jordan
instance is supplied.

The off-diagonal slot indexed by `j` is opposite diagonal position `j`: it lies in
that idempotent's zero-space and in each other diagonal idempotent's half-space.
-/

public section

namespace TauCeti.AlbertAlgebra

open Jordan

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Every diagonal idempotent belongs to its own `1`-Peirce space. -/
theorem diagIdempotent_mem_peirceSpace_one (i : Fin 3) :
    diagIdempotent R i ∈ peirceSpace R (diagIdempotent R i) 1 := by
  simp [mem_peirceSpace]

/-- Distinct diagonal idempotents belong to each other's `0`-Peirce space. -/
theorem diagIdempotent_mem_peirceSpace_zero {i j : Fin 3} (h : i ≠ j) :
    diagIdempotent R j ∈ peirceSpace R (diagIdempotent R i) 0 := by
  simp [mem_peirceSpace, h]

/-- The opposite off-diagonal slot lies in the `0`-Peirce space. -/
theorem offDiagSingle_mem_peirceSpace_zero (i : Fin 3) (a : Octonion R) :
    offDiagSingle i a ∈ peirceSpace R (diagIdempotent R i) 0 := by
  simp [mem_peirceSpace]

/-- Each incident off-diagonal slot lies in the half-Peirce space. -/
theorem offDiagSingle_mem_peirceSpace_invOf_two {i j : Fin 3} (h : i ≠ j) (a : Octonion R) :
    offDiagSingle j a ∈ peirceSpace R (diagIdempotent R i) ⅟(2 : R) := by
  simp [mem_peirceSpace, h]

end TauCeti.AlbertAlgebra
