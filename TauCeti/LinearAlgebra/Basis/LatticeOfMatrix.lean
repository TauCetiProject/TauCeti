/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# The lattice of a matrix in a basis

Given a basis `ω : Basis ι A M` of an `A`-module `M` with `ι` finite, a matrix `H` with rows indexed
by `ι` and finitely many columns determines the `A`-submodule of `M` whose `ω`-coordinates form the
column span of `H`. For `A = ℤ` this is the lattice in `M` cut out by the integer matrix `H`.

## Main definitions

* `Module.Basis.latticeOfMatrix ω H`: the `A`-submodule spanned by the vectors whose
  `ω`-coordinates are the columns of the matrix `H`.

## Main results

* `Module.Basis.mem_latticeOfMatrix`, `Module.Basis.latticeOfMatrix_eq_iff`: membership in and
  equality with the lattice of `H`, read in `ω`-coordinates.
* `Module.Basis.latticeOfMatrix_eq_span`: the lattice of `H` is spanned by the vectors
  `∑ i, H i j • ω i`.
-/

public section

open Matrix

namespace Module.Basis

variable {A M ι κ : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M] [Fintype ι] [Fintype κ]
  (ω : Basis ι A M)

/-- The *lattice* of a matrix `H` read in the basis `ω`: the `A`-submodule spanned by the vectors
`∑ i, H i j • ω i` whose `ω`-coordinates are the columns of `H`, see
`Module.Basis.latticeOfMatrix_eq_span`. -/
noncomputable def latticeOfMatrix (H : Matrix ι κ A) : Submodule A M :=
  (LinearMap.range H.mulVecLin).map (ω.equivFun.symm : (ι → A) →ₗ[A] M)

variable {ω} {H : Matrix ι κ A}

/-- A vector lies in the lattice of `H` if and only if its `ω`-coordinates are an `A`-linear
combination of the columns of `H`. -/
@[simp]
theorem mem_latticeOfMatrix {x : M} : x ∈ ω.latticeOfMatrix H ↔ ∃ c, H *ᵥ c = ω.equivFun x := by
  simp [latticeOfMatrix]

/-- The lattice of `H` is `N` if and only if the column lattice of `H` is the lattice of
`ω`-coordinates of `N`. -/
theorem latticeOfMatrix_eq_iff {N : Submodule A M} :
    ω.latticeOfMatrix H = N ↔
      LinearMap.range H.mulVecLin = N.map (ω.equivFun : M →ₗ[A] ι → A) := by
  rw [latticeOfMatrix, Submodule.map_symm_eq_iff, eq_comm]

variable (ω H) in
/-- The lattice of `H` is spanned by the vectors `∑ i, H i j • ω i` whose `ω`-coordinates are the
columns of `H`. -/
theorem latticeOfMatrix_eq_span :
    ω.latticeOfMatrix H = Submodule.span A (Set.range fun j ↦ ∑ i, H i j • ω i) := by
  rw [latticeOfMatrix, range_mulVecLin, Submodule.map_span, ← Set.range_comp]
  congr 2
  ext j
  rw [Function.comp_apply, LinearEquiv.coe_coe, equivFun_symm_apply]
  simp

variable (ω) in
/-- The lattice of the identity matrix is the whole module. -/
@[simp]
theorem latticeOfMatrix_one [DecidableEq ι] : ω.latticeOfMatrix (1 : Matrix ι ι A) = ⊤ := by
  simp [latticeOfMatrix]

/-- The lattice of `H` is zero if and only if `H` is the zero matrix. -/
@[simp]
theorem latticeOfMatrix_eq_bot_iff : ω.latticeOfMatrix H = ⊥ ↔ H = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, latticeOfMatrix]⟩
  rw [latticeOfMatrix_eq_iff, Submodule.map_bot] at h
  ext i j
  have hj : H.col j = 0 := (Submodule.mem_bot A).mp (h ▸ H.col_mem_range_mulVecLin j)
  simpa using congrFun hj i

end Module.Basis
