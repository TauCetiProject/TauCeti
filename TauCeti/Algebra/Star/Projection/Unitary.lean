/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.Abel

/-!
# Unitary conjugation and reflections of star projections

Unitary conjugation preserves star projections in any star monoid, and in any star ring a star
projection `p` gives rise to the self-adjoint unitary reflection `1 - 2 * p`. Conversely, over a
characteristic-zero division ring with trivial star, every self-adjoint unitary `u` determines its
`-1`-eigenprojection `(1 / 2 : 𝕜) • (1 - u)`.

## Main results

* `IsStarProjection.star_right_conjugate`, `IsStarProjection.star_left_conjugate`: `u * p * star u`
  and `star u * p * u` are star projections whenever `p` is a star projection and `u` is unitary.
* `IsStarProjection.one_sub_two_mul_mem_unitary`: `1 - 2 * p ∈ unitary R` for a star projection `p`.
* `IsStarProjection.half_smul_one_sub`: `(1 / 2 : 𝕜) • (1 - u)` is a star projection for any
  self-adjoint `u : unitary A`.
-/

public section

namespace IsStarProjection

/-- Unitary conjugation `u * p * star u` preserves star projections. -/
theorem star_right_conjugate {R : Type*} [Monoid R] [StarMul R] {p : R}
    (hp : IsStarProjection p) (u : unitary R) :
    IsStarProjection ((u : R) * p * star (u : R)) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    calc (u : R) * p * star (u : R) * ((u : R) * p * star (u : R))
        = (u : R) * p * (star (u : R) * (u : R)) * p * star (u : R) := by simp only [mul_assoc]
      _ = (u : R) * (p * p) * star (u : R) := by
            rw [Unitary.coe_star_mul_self, mul_one, mul_assoc (u : R) p p]
      _ = (u : R) * p * star (u : R) := by rw [hp.isIdempotentElem.eq]
  · rw [IsSelfAdjoint, star_mul, star_mul, star_star, hp.isSelfAdjoint.star_eq, mul_assoc]

/-- Unitary conjugation `star u * p * u` preserves star projections. -/
theorem star_left_conjugate {R : Type*} [Monoid R] [StarMul R] {p : R}
    (hp : IsStarProjection p) (u : unitary R) :
    IsStarProjection (star (u : R) * p * (u : R)) := by
  simpa using hp.star_right_conjugate (star u)

/-- For a star projection `p`, `1 - 2 * p` is a unitary element. -/
theorem one_sub_two_mul_mem_unitary {R : Type*} [Ring R] [StarRing R] {p : R}
    (hp : IsStarProjection p) : 1 - 2 * p ∈ unitary R := by
  have h : -(2 * p - 1) = 1 - 2 * p := by abel
  rw [← h]
  exact SetLike.coe_mem (-⟨2 * p - 1, hp.two_mul_sub_one_mem_unitary⟩ : unitary R)

/-- For a self-adjoint unitary `u`, `(1 / 2 : 𝕜) • (1 - u)` is a star projection. -/
theorem half_smul_one_sub (𝕜 : Type*) {A : Type*}
    [DivisionRing 𝕜] [CharZero 𝕜] [Star 𝕜] [TrivialStar 𝕜]
    [Ring A] [StarRing A] [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [StarModule 𝕜 A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) :
    IsStarProjection ((1 / 2 : 𝕜) • (1 - (u : A))) := by
  have hu2 : (u : A) * (u : A) = 1 := by
    simpa [hu.star_eq] using Unitary.coe_mul_star_self u
  have h1u : (1 - (u : A)) * (1 - (u : A)) = (2 : 𝕜) • (1 - (u : A)) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hu2, two_smul]
    abel
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, smul_mul_smul_comm, h1u, smul_smul, one_div, mul_assoc,
      inv_mul_cancel₀ two_ne_zero, mul_one]
  · simp [IsSelfAdjoint, star_smul, hu.star_eq]

end IsStarProjection
