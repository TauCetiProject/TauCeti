/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
import TauCeti.LinearAlgebra.Matrix.UnitaryTransvection

/-!
# Rank-one unitary perturbations along a unit vector

Over an additively cancellative commutative `StarRing` `R`, let `ρ : n → R` satisfy
`star ρ ⬝ᵥ ρ = 1` and let `A : R` satisfy `star (1 + A) * (1 + A) = 1`. The rank-one perturbation
`U = 1 + A • Matrix.vecMulVec ρ (star ρ)`—which scales `ρ` by `1 + A` and fixes its orthogonal
complement—is a unitary transvection for the identity Gram matrix, so `Uᴴ * U = 1`
(`TauCeti.conjTranspose_mul_one_add_smul_vecMulVec`), and over a commutative `StarRing`,
`U ∈ Matrix.unitaryGroup n R` (`TauCeti.one_add_smul_vecMulVec_mem_unitaryGroup`). When `A = -2`
this recovers the Householder reflection along `ρ`.

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
theorem conjTranspose_mul_one_add_smul_vecMulVec {R n : Type*} [CommSemiring R] [IsCancelAdd R]
    [StarRing R] [Fintype n] [DecidableEq n] {ρ : n → R} {A : R}
    (hρ : star ρ ⬝ᵥ ρ = 1) (hA : star (1 + A) * (1 + A) = 1) :
    (1 + A • vecMulVec ρ (star ρ))ᴴ * (1 + A • vecMulVec ρ (star ρ)) = 1 := by
  have hstar : starRingEnd R ∘ ρ = star ρ := funext fun _ ↦ starRingEnd_apply _
  have h_sum : A + 1 * starRingEnd R A + 1 * A * starRingEnd R A *
      ((starRingEnd R ∘ ρ) ⬝ᵥ ((1 : Matrix n n R) *ᵥ ρ)) = 0 := by
    have h1 : 1 + (A + star A + A * star A) = 1 + 0 := by
      simpa [star_add, star_one, add_mul, mul_add, add_assoc, mul_comm] using hA
    simpa [hstar, hρ, starRingEnd_apply] using add_left_cancel h1
  have hQ : ((1 : Matrix n n R).map (starRingEnd R))ᵀ = (1 : R) • (1 : Matrix n n R) := by
    ext i j; by_cases hij : i = j <;> simp [hij, Ne.symm]
  have h := transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero
    (Q := (1 : Matrix n n R)) (σ := starRingEnd R) (v := ρ) (a := A)
    star_involutive hQ h_sum
  have hU : (1 : Matrix n n R).unitaryTransvection (starRingEnd R) ρ A =
      1 + A • vecMulVec ρ (star ρ) := by
    ext i j; simp [Matrix.unitaryTransvection_def, vecMulVec_apply, starRingEnd_apply]
  have hconj : ((1 + A • vecMulVec ρ (star ρ)).map (starRingEnd R))ᵀ =
      (1 + A • vecMulVec ρ (star ρ))ᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply, starRingEnd_apply]
  simpa [hU, hconj] using h

/-- The rank-one perturbation `1 + A • vecMulVec ρ (star ρ)` lies in
`Matrix.unitaryGroup n R`. -/
theorem one_add_smul_vecMulVec_mem_unitaryGroup {R n : Type*} [CommRing R] [StarRing R]
    [Fintype n] [DecidableEq n] {ρ : n → R} {A : R}
    (hρ : star ρ ⬝ᵥ ρ = 1) (hA : star (1 + A) * (1 + A) = 1) :
    1 + A • vecMulVec ρ (star ρ) ∈ Matrix.unitaryGroup n R :=
  Matrix.mem_unitaryGroup_iff'.mpr (conjTranspose_mul_one_add_smul_vecMulVec hρ hA)

end TauCeti
