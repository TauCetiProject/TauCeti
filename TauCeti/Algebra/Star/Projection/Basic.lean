/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing

/-!
# Basic lemmas for star projections

Elementary algebraic facts about star projections (`IsStarProjection`) in star rings and star
multiplicative structures:

* `IsStarProjection.half_one_sub_of_mul_self_eq_one`: `(2 : 𝕜)⁻¹ • (1 - w)` is a star projection
  for any self-adjoint involution `w`.
* `IsStarProjection.of_map_injective`: an injective star-multiplicative map reflects star
  projections.
-/

public section

/-- For a self-adjoint involution `w` (`w * w = 1`), `(2 : 𝕜)⁻¹ • (1 - w)` is a star projection. -/
theorem IsStarProjection.half_one_sub_of_mul_self_eq_one {𝕜 A : Type*} [DivisionRing 𝕜]
    [CharZero 𝕜] [StarRing 𝕜] [Ring A] [StarRing A] [Module 𝕜 A] [IsScalarTower 𝕜 A A]
    [SMulCommClass 𝕜 A A] [StarModule 𝕜 A]
    {w : A} (hw : w * w = 1) (hsa : IsSelfAdjoint w) :
    IsStarProjection ((2 : 𝕜)⁻¹ • (1 - w)) where
  isIdempotentElem := by
    rw [IsIdempotentElem, smul_mul_smul_comm]
    have hmul : (1 - w) * (1 - w) = (2 : 𝕜) • (1 - w) := by
      calc (1 - w) * (1 - w) = 1 - w - w + w * w := by noncomm_ring
        _ = (2 : 𝕜) • (1 - w) := by rw [hw, two_smul]; abel
    rw [hmul, smul_smul, mul_assoc, inv_mul_cancel₀ (by simp), mul_one]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff, star_smul, star_inv₀, star_ofNat, star_sub, star_one, hsa.star_eq]

/-- An injective star-multiplicative map reflects star projections. -/
theorem IsStarProjection.of_map_injective {A B F : Type*} [Mul A] [Star A] [Mul B] [Star B]
    [FunLike F A B] [MulHomClass F A B] [StarHomClass F A B]
    {f : F} (hf : Function.Injective f) {p : A} (hp : IsStarProjection (f p)) :
    IsStarProjection p where
  isIdempotentElem := hf (by simpa only [map_mul] using hp.isIdempotentElem.eq)
  isSelfAdjoint := hf (by simpa only [map_star] using hp.isSelfAdjoint.star_eq)
