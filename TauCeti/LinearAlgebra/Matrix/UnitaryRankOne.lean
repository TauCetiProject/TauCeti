/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Basic

/-!
# Rank-one unitary perturbations along a unit vector

Over a commutative `StarRing` `R`, let `ρ : n → R` satisfy `star ρ ⬝ᵥ ρ = 1` and let `A : R`
satisfy `star (1 + A) * (1 + A) = 1`. The rank-one projection `Q = Matrix.vecMulVec ρ (star ρ)` is
Hermitian and idempotent, so `1 + A • Q`—which scales `ρ` by `1 + A` and fixes its orthogonal
complement—is unitary: `(1 + A • Q)ᴴ * (1 + A • Q) = 1`, hence
`1 + A • Q ∈ Matrix.unitaryGroup n R`. When `A = -2` this recovers the Householder reflection
along `ρ`.

## Provenance

Extracted and generalized from `grh-lean`
(https://github.com/lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC),
file `src/New/UpperBound/Seesaw/NeighbourLattice.lean`
(`conjTranspose_mul_one_add_smul_vecMulVec`).
-/

public section

namespace TauCeti

open Matrix

/-- The matrix `1 + A • vecMulVec ρ (star ρ)` scaling a unit vector `ρ` by a norm-one factor
`1 + A` and fixing its orthogonal complement satisfies `Uᴴ * U = 1`. -/
theorem conjTranspose_mul_one_add_smul_vecMulVec {R n : Type*} [CommRing R] [StarRing R]
    [Fintype n] [DecidableEq n] {ρ : n → R} {A : R}
    (hρ : star ρ ⬝ᵥ ρ = 1) (hA : star (1 + A) * (1 + A) = 1) :
    (1 + A • vecMulVec ρ (star ρ))ᴴ * (1 + A • vecMulVec ρ (star ρ)) = 1 := by
  set Q : Matrix n n R := vecMulVec ρ (star ρ) with hQ
  have h_adj : Qᴴ = Q := by rw [hQ, conjTranspose_vecMulVec, star_star]
  have h_sq : Q * Q = Q := by rw [hQ, vecMulVec_mul_vecMulVec, hρ, one_smul]
  have h_sum : star A + A + star A * A = 0 := by
    have h1 : 1 + (star A + A + star A * A) = 1 + 0 := by
      simpa [star_add, star_one, add_mul, mul_add, add_assoc] using hA
    exact add_left_cancel h1
  calc
    (1 + A • Q)ᴴ * (1 + A • Q) = 1 + (star A + A + star A * A) • Q := by
      simp [h_adj, add_mul, mul_add, smul_smul, h_sq, add_smul, add_assoc, mul_comm]
    _ = 1 := by simp [h_sum]

/-- The rank-one perturbation `1 + A • vecMulVec ρ (star ρ)` lies in
`Matrix.unitaryGroup n R`. -/
theorem one_add_smul_vecMulVec_mem_unitaryGroup {R n : Type*} [CommRing R] [StarRing R]
    [Fintype n] [DecidableEq n] {ρ : n → R} {A : R}
    (hρ : star ρ ⬝ᵥ ρ = 1) (hA : star (1 + A) * (1 + A) = 1) :
    1 + A • vecMulVec ρ (star ρ) ∈ Matrix.unitaryGroup n R :=
  Matrix.mem_unitaryGroup_iff'.mpr (conjTranspose_mul_one_add_smul_vecMulVec hρ hA)

end TauCeti
