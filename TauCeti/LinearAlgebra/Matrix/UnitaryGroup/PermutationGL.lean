/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary

/-!
# Unitary permutation matrices as invertible matrices

A permutation is embedded in the unitary group by `Matrix.permutationUnitary` and in the general
linear group by `TauCeti.permutationGL`. This file records that the two embeddings agree once a
unitary matrix is viewed as an invertible matrix via `Unitary.toUnits`
(`TauCeti.toUnits_permutationUnitary`). It is kept apart from both definitions so that the basic
unitary-group file does not import the diagonal-normalizer theory where `permutationGL` lives.

## Main results

* `TauCeti.toUnits_permutationUnitary`: as an invertible matrix, `Matrix.permutationUnitary σ`
  is `TauCeti.permutationGL σ`.
* `TauCeti.permutationGL_mem_unitarySubgroup`: permutation matrices lie in the unitary subgroup
  of the general linear group.
-/

public section

namespace TauCeti

open Matrix

/-- As an invertible matrix, the unitary permutation matrix of a permutation is its permutation
matrix in the general linear group. -/
@[simp]
theorem toUnits_permutationUnitary {R : Type*} [CommRing R] [StarRing R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (σ : Equiv.Perm ι) :
    Unitary.toUnits (permutationUnitary (R := R) σ) = permutationGL σ :=
  Units.ext <| by rw [Unitary.val_toUnits_apply, permutationGL_coe, coe_permutationUnitary]

/-- A permutation matrix lies in the unitary subgroup of the general linear group; over a ring
with trivial star, such as `ℝ`, this is the orthogonal group. -/
theorem permutationGL_mem_unitarySubgroup {R : Type*} [CommRing R] [StarRing R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    permutationGL σ ∈ unitarySubgroup (GL ι R) := by
  rw [mem_unitarySubgroup_GL_iff_mem_unitaryGroup, ← toUnits_permutationUnitary,
    Unitary.val_toUnits_apply]
  exact (permutationUnitary σ).property

end TauCeti
