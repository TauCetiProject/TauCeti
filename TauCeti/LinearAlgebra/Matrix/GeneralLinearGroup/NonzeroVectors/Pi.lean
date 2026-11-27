/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UnimodularFrame.Semilocal

/-!
# Vectors over a product of fields that are nonzero at every place

For a finite set `P` of places and a finite field `𝔽`, a vector `y` of `m → P → 𝔽` is *primitive*
if it is nonzero at every place: for every `w ∈ P` the vector `fun i ↦ y i w` of `m → 𝔽` is
nonzero. These are the placewise version of the nonzero vectors `TauCeti.nonzeroVectors` of
`m → 𝔽`. There are `(|𝔽| ^ |m| - 1) ^ |P|` of them. As a nonzero vector over a field is carried
to any other by an invertible matrix (`TauCeti.exists_smul_eq_of_ne_zero`), a primitive vector is
a column of an invertible matrix over `P → 𝔽`: it has a left inverse, and `GL` acts transitively
on such vectors over the semilocal ring `P → 𝔽` (`TauCeti.exists_smul_eq_of_mul_eq_one`). Along
a surjective reduction onto `P → 𝔽` that reflects units, such as the reduction of a product of
complete local rings onto their residue fields, it is then a column of the reduction of an
integral invertible matrix.

## Main definitions

* `TauCeti.primitiveVectors`: the vectors of `m → P → 𝔽` that are nonzero at every place.

## Main results

* `TauCeti.card_primitiveVectors`: there are `(|𝔽| ^ |m| - 1) ^ |P|` primitive vectors.
* `TauCeti.exists_col_eq_of_mem_primitiveVectors`: a primitive vector is any given column of an
  invertible matrix.
* `TauCeti.exists_map_col_eq_of_mem_primitiveVectors`: a primitive vector is any given column of
  the reduction of an integral invertible matrix, along a surjective reduction that reflects
  units.
-/

public section

open Matrix Finset

namespace TauCeti

variable {m : Type*} [Fintype m] [DecidableEq m] {P 𝔽 : Type*} [Fintype P] [DecidableEq P]
  [Fintype 𝔽] [DecidableEq 𝔽]

section Zero

variable [Zero 𝔽]

variable (m P 𝔽) in
/-- The *primitive* vectors of `m → P → 𝔽`: those that are nonzero at every place `w ∈ P`. -/
def primitiveVectors : Finset (m → P → 𝔽) :=
  univ.filter fun y ↦ ∀ w, (fun i ↦ y i w) ≠ 0

@[simp]
theorem mem_primitiveVectors {y : m → P → 𝔽} :
    y ∈ primitiveVectors m P 𝔽 ↔ ∀ w, ∃ i, y i w ≠ 0 := by
  simp [primitiveVectors, funext_iff]

/-- There are `(|𝔽| ^ |m| - 1) ^ |P|` primitive vectors. -/
theorem card_primitiveVectors :
    #(primitiveVectors m P 𝔽) = (Fintype.card 𝔽 ^ Fintype.card m - 1) ^ Fintype.card P := by
  rw [card_equiv (Equiv.piComm fun (_ : m) (_ : P) ↦ 𝔽)
    (t := Fintype.piFinset fun _ : P ↦ univ.filter fun v : m → 𝔽 ↦ v ≠ 0)
    (fun y ↦ by simp [primitiveVectors, Equiv.piComm])]
  simp [filter_ne']

end Zero

variable [Field 𝔽]

/-- A primitive vector is the column `l` of an invertible matrix. -/
theorem exists_col_eq_of_mem_primitiveVectors {y : m → P → 𝔽}
    (hy : y ∈ primitiveVectors m P 𝔽) (l : m) :
    ∃ g : GL m (P → 𝔽), (g : Matrix m m (P → 𝔽)).col l = y := by
  classical
  -- a row `s` with `s ⬝ᵥ y = 1`
  choose i hi using mem_primitiveVectors.1 hy
  set s : m → P → 𝔽 := fun j w ↦ if j = i w then (y j w)⁻¹ else 0
  have hs : s ⬝ᵥ y = 1 := by
    ext w
    simp [s, dotProduct, Finset.sum_apply, hi w]
  have h1 : replicateRow Unit (Pi.single l 1 : m → P → 𝔽) *
      replicateCol Unit (Pi.single l (1 : P → 𝔽)) = 1 := by
    ext
    simp
  have h2 : replicateRow Unit s * replicateCol Unit y = 1 := by
    ext
    simp [hs]
  obtain ⟨g, hg⟩ := exists_smul_eq_of_mul_eq_one h1 h2
  refine ⟨g, ?_⟩
  rw [GeneralLinearGroup.smul_def, ← replicateCol_mulVec, mulVec_single_one] at hg
  exact funext fun j ↦ congrFun₂ hg j ()

/-- Over a reduction that is surjective and reflects units, a primitive vector is the column
`l` of the reduction of an integral invertible matrix. -/
theorem exists_map_col_eq_of_mem_primitiveVectors {A : Type*} [CommRing A]
    (red : A →+* (P → 𝔽)) [IsLocalHom red] (hred : Function.Surjective red) {y : m → P → 𝔽}
    (hy : y ∈ primitiveVectors m P 𝔽) (l : m) :
    ∃ a : GL m A, (GeneralLinearGroup.map red a : Matrix m m (P → 𝔽)).col l = y := by
  obtain ⟨g, hg⟩ := exists_col_eq_of_mem_primitiveVectors hy l
  obtain ⟨a, rfl⟩ := GeneralLinearGroup.map_surjective red hred g
  exact ⟨a, hg⟩

end TauCeti
