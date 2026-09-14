/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Pi

/-!
# Linear and additive codes

This file fixes the carrier conventions for finite-coordinate codes. A linear code over a field
is a submodule of the word space, while an additive code over a commutative additive group is an
additive subgroup. Consequently, the lattice operations, maps, comaps, and membership notation
are exactly those of `Submodule` and `AddSubgroup` rather than parallel wrappers.

These aliases let matrix presentations, Hamming invariants, and duality share Mathlib's existing
subobject APIs. Coordinate types remain arbitrary finite types; particular codes may later use
`Fin n` to display a conventional matrix.
-/

public section

namespace TauCeti

/-- A linear code over `F` with coordinate set `ι` is a linear subspace of the word space
`ι → F`. -/
abbrev LinearCode (F ι : Type*) [Field F] := Submodule F (ι → F)

/-- An additive code over `A` with coordinate set `ι` is an additive subgroup of the word space
`ι → A`. No scalar closure is implicit in this notion. -/
abbrev AdditiveCode (A ι : Type*) [AddCommGroup A] := AddSubgroup (ι → A)

end TauCeti
