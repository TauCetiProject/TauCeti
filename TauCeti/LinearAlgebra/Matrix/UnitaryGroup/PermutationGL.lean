/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup

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

end TauCeti
