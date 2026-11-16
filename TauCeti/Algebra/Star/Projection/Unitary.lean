/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.Abel
import TauCeti.Algebra.Group.Idempotent

/-!
# Unitary conjugation and reflections of star projections

Unitary conjugation preserves and reflects star projections in any star monoid, and in any star
ring a star projection `p` gives rise to the self-adjoint unitary reflection `1 - 2 * p`.
Conversely, over any division semiring in which `2 ≠ 0`, every self-adjoint unitary `u` determines
its `-1`-eigenprojection `(1 / 2 : 𝕜) • (1 - u)`.

## Main results

* `IsStarProjection.star_right_conjugate`, `IsStarProjection.star_left_conjugate`,
  `isStarProjection_star_right_conjugate_iff`, `isStarProjection_star_left_conjugate_iff`:
  `u * p * star u` and `star u * p * u` are star projections iff `p` is a star projection.
* `IsStarProjection.one_sub_two_mul_mem_unitary`: `1 - 2 * p ∈ unitary R` for a star projection `p`.
* `IsStarProjection.half_smul_one_sub_of_isSelfAdjoint`: `(1 / 2 : 𝕜) • (1 - u)` is a star
  projection for any self-adjoint `u : unitary A` when `2 ≠ 0` in `𝕜`.
-/

public section

namespace IsStarProjection

/-- Unitary conjugation `u * p * star u` preserves star projections. -/
theorem star_right_conjugate {R : Type*} [Monoid R] [StarMul R] {p : R}
    (hp : IsStarProjection p) (u : unitary R) :
    IsStarProjection ((u : R) * p * star (u : R)) :=
  ⟨hp.isIdempotentElem.mul_mul_of_mul_eq_one (Unitary.coe_star_mul_self u),
    hp.isSelfAdjoint.conjugate (u : R)⟩

/-- Unitary conjugation `star u * p * u` preserves star projections. -/
theorem star_left_conjugate {R : Type*} [Monoid R] [StarMul R] {p : R}
    (hp : IsStarProjection p) (u : unitary R) :
    IsStarProjection (star (u : R) * p * (u : R)) := by
  simpa using hp.star_right_conjugate (star u)

/-- An element `u * p * star u` conjugated by a unitary `u` is a star projection iff `p` is. -/
@[simp]
theorem _root_.isStarProjection_star_right_conjugate_iff {R : Type*} [Monoid R] [StarMul R]
    (u : unitary R) {p : R} :
    IsStarProjection ((u : R) * p * star (u : R)) ↔ IsStarProjection p :=
  ⟨fun h ↦ by
    have h' := h.star_left_conjugate u
    rwa [← mul_assoc, ← mul_assoc, Unitary.coe_star_mul_self, one_mul, mul_assoc,
      Unitary.coe_star_mul_self, mul_one] at h',
    fun h ↦ h.star_right_conjugate u⟩

/-- An element `star u * p * u` conjugated by a unitary `u` is a star projection iff `p` is. -/
@[simp]
theorem _root_.isStarProjection_star_left_conjugate_iff {R : Type*} [Monoid R] [StarMul R]
    (u : unitary R) {p : R} :
    IsStarProjection (star (u : R) * p * (u : R)) ↔ IsStarProjection p := by
  simpa using isStarProjection_star_right_conjugate_iff (star u) (p := p)

/-- For a star projection `p`, `1 - 2 * p` is a unitary element. -/
theorem one_sub_two_mul_mem_unitary {R : Type*} [Ring R] [StarRing R] {p : R}
    (hp : IsStarProjection p) : 1 - 2 * p ∈ unitary R := by
  have h : -(2 * p - 1) = 1 - 2 * p := by abel
  rw [← h]
  exact SetLike.coe_mem (-⟨2 * p - 1, hp.two_mul_sub_one_mem_unitary⟩ : unitary R)

/-- For a self-adjoint unitary `u`, `(1 / 2 : 𝕜) • (1 - u)` is a star projection. -/
theorem half_smul_one_sub_of_isSelfAdjoint (𝕜 : Type*) {A : Type*}
    [DivisionSemiring 𝕜] [NeZero (2 : 𝕜)]
    [Ring A] [StarRing A] [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A)) :
    IsStarProjection ((1 / 2 : 𝕜) • (1 - (u : A))) := by
  set y : A := (1 / 2 : 𝕜) • (1 - (u : A))
  have h2 : (2 : 𝕜) ≠ 0 := NeZero.ne (2 : 𝕜)
  have h2y : (2 : 𝕜) • y = 1 - (u : A) := by
    rw [smul_smul, one_div, mul_inv_cancel₀ h2, one_smul]
  have hu2 : (u : A) * (u : A) = 1 := by
    simpa [hu.star_eq] using Unitary.coe_mul_star_self u
  have h1u : (1 - (u : A)) * (1 - (u : A)) = (2 : 𝕜) • (1 - (u : A)) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hu2, two_smul]
    abel
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    dsimp only [y]
    rw [smul_mul_assoc, mul_smul_comm, h1u, smul_smul, smul_smul, one_div, mul_assoc,
      inv_mul_cancel₀ h2, mul_one]
  · rw [IsSelfAdjoint]
    calc star y
        = (1 / 2 : 𝕜) • ((2 : 𝕜) • star y) := by
            rw [smul_smul, one_div, inv_mul_cancel₀ h2, one_smul]
      _ = (1 / 2 : 𝕜) • star ((2 : 𝕜) • y) := by
            rw [two_smul, two_smul, star_add]
      _ = y := by
            rw [h2y, star_sub, star_one, hu.star_eq]

end IsStarProjection
