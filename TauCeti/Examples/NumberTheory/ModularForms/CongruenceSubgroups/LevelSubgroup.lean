/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.LevelSubgroup
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Checks for the levels `Γ₁(5)` and `Γ₁^μ(5)`

The coarse degree of `X_H` over the `j`-line is the projective index, not the index: for the
levels `Γ₁ = TauCeti.GL2Gamma1 (ZMod 5)` and `Γ₁^μ = TauCeti.GL2Mirabolic (ZMod 5)` the index is
`24` but the projective index is `12`, because `-1` lies in neither.

* `[GL₂(ℤ / 5) : Γ₁] = 24` and `[GL₂(ℤ / 5) : ±Γ₁] = 12`.
* `[GL₂(ℤ / 5) : Γ₁^μ] = 24` and `[GL₂(ℤ / 5) : ±Γ₁^μ] = 12`.
-/

public section

open CongruenceSubgroup

namespace TauCeti.Examples.LevelSubgroup

/-- `[SL(2, ℤ) : Γ₁(5)] = φ(5) (5 + 1) = 24`. -/
theorem index_gamma1_five : (Gamma1 5).index = 24 := by
  rw [Gamma1_prime_index 5 Nat.prime_five]

/-- The level `Γ₁(5)` has index `24`. -/
theorem index_GL2Gamma1_five : (GL2Gamma1 (ZMod 5)).index = 24 := by
  rw [index_GL2Gamma1_zmod, index_gamma1_five]

/-- The level `Γ₁(5)` has projective index `12`, half its index. -/
theorem projectiveIndex_GL2Gamma1_five : (GL2Gamma1 (ZMod 5)).projectiveIndex = 12 := by
  have := two_mul_projectiveIndex_GL2Gamma1_zmod 5 (by norm_num)
  rw [index_gamma1_five] at this
  omega

/-- The level `Γ₁^μ(5)` has index `24`. -/
theorem index_GL2Mirabolic_five : (GL2Mirabolic (ZMod 5)).index = 24 := by
  rw [index_GL2Mirabolic_zmod, index_gamma1_five]

/-- The level `Γ₁^μ(5)` has projective index `12`, half its index. -/
theorem projectiveIndex_GL2Mirabolic_five : (GL2Mirabolic (ZMod 5)).projectiveIndex = 12 := by
  have := two_mul_projectiveIndex_GL2Mirabolic_zmod 5 (by norm_num)
  rw [index_gamma1_five] at this
  omega

end TauCeti.Examples.LevelSubgroup
