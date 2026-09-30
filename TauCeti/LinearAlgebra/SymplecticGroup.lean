/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Block matrices in the symplectic group

Membership in Mathlib's `Matrix.symplecticGroup` of three families of block matrices, each a
specialisation of `SymplecticGroup.fromBlocks_mem_iff`:

* `SymplecticGroup.fromBlocks_upper_mem`: `fromBlocks 1 B 0 1` for symmetric `B`;
* `SymplecticGroup.fromBlocks_lower_mem`: `fromBlocks 1 0 C 1` for symmetric `C`;
* `SymplecticGroup.fromBlocks_diagonal_mem`: `fromBlocks A 0 0 D` when `Aᵀ * D = 1`.
-/

public section

open Matrix

namespace SymplecticGroup

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

/-- An upper unitriangular block matrix is symplectic when its upper-right block is symmetric. -/
theorem fromBlocks_upper_mem {B : Matrix l l R} (hB : Bᵀ = B) :
    fromBlocks 1 B 0 1 ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hB]

/-- A lower unitriangular block matrix is symplectic when its lower-left block is symmetric. -/
theorem fromBlocks_lower_mem {C : Matrix l l R} (hC : Cᵀ = C) :
    fromBlocks 1 0 C 1 ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hC]

/-- A block-diagonal matrix is symplectic when its diagonal blocks satisfy the defining inverse
transpose relation. -/
theorem fromBlocks_diagonal_mem {A D : Matrix l l R} (hAD : Aᵀ * D = 1) :
    fromBlocks A 0 0 D ∈ symplecticGroup l R := by
  rw [fromBlocks_mem_iff]
  simp [hAD]

end SymplecticGroup
