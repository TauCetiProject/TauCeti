/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Splitting quadratic algebras

The idempotent-generator algebra `QuadraticAlgebra R 0 1` is isomorphic to `R × R`.
When `2` is invertible and `a` is the square of a unit `u`, the algebra
`QuadraticAlgebra R a 0` also splits: its two coordinates evaluate `ω` at `u` and `-u`.
The inverse uses the half-sum and the rescaled half-difference.

The second isomorphism is assembled from Mathlib's changes of generator, so it applies
without a field hypothesis on `R`.
-/

public section

namespace QuadraticAlgebra

/-- The algebra with an idempotent generator is the product algebra. -/
@[expose, simps!]
def algEquivProd {R : Type*} [CommRing R] :
    QuadraticAlgebra R 0 1 ≃ₐ[R] R × R where
  toFun z := (z.re + z.im, z.re)
  invFun z := ⟨z.2, z.1 - z.2⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by
    ext <;> simp
    ring
  map_add' z w := by
    ext <;> simp
    ring
  commutes' r := by ext <;> simp

/-- Over a ring with two invertible, a quadratic algebra of unit-square parameter splits. -/
def algEquivProdOfSq {R : Type*} [CommRing R] [Invertible (2 : R)] {a : R}
    (u : Rˣ) (ha : a = (u : R) ^ 2) : QuadraticAlgebra R a 0 ≃ₐ[R] R × R :=
  (changeGeneratorEquiv 1 0 u 0 (by simpa using ha) (by ring)).trans
    ((changeGeneratorEquiv 0 1 (unitOfInvertible (2 : R)) (-1)
      (by simp only [val_unitOfInvertible]; ring)
      (by simp only [val_unitOfInvertible]; ring)).trans algEquivProd)

/-- The square-root generator maps to the two opposite square roots. -/
private theorem algEquivProdOfSq_omega {R : Type*} [CommRing R] [Invertible (2 : R)] {a : R}
    (u : Rˣ) (ha : a = (u : R) ^ 2) :
    algEquivProdOfSq u ha ω = ((u : R), -(u : R)) := by
  ext <;> simp [algEquivProdOfSq, algEquivProd, changeGeneratorEquiv, changeGenerator,
    lift_apply_apply, Algebra.smul_def]
  all_goals ring

/-- Splitting evaluates a quadratic-algebra element at the two opposite square roots. -/
@[simp]
theorem algEquivProdOfSq_apply {R : Type*} [CommRing R] [Invertible (2 : R)] {a : R}
    (u : Rˣ) (ha : a = (u : R) ^ 2) (z : QuadraticAlgebra R a 0) :
    algEquivProdOfSq u ha z = (z.re + (u : R) * z.im, z.re - (u : R) * z.im) := by
  rw [← re_smul_add_im_smul z, map_add, map_smul, map_one, map_smul,
    algEquivProdOfSq_omega]
  ext <;> simp [Algebra.smul_def, mul_comm, sub_eq_add_neg]

/-- The inverse splitting map recovers the half-sum and rescaled half-difference. -/
@[simp]
theorem algEquivProdOfSq_symm_apply {R : Type*} [CommRing R] [Invertible (2 : R)]
    {a : R} (u : Rˣ) (ha : a = (u : R) ^ 2) (z : R × R) :
    (algEquivProdOfSq u ha).symm z =
      ⟨⅟(2 : R) * (z.1 + z.2), (u⁻¹ : Rˣ) * ⅟(2 : R) * (z.1 - z.2)⟩ := by
  apply (algEquivProdOfSq u ha).injective
  rw [AlgEquiv.apply_symm_apply, algEquivProdOfSq_apply]
  ext <;> dsimp
  · simp only [mul_assoc, Units.mul_inv_cancel_left]
    linear_combination -z.1 * (invOf_mul_self (2 : R))
  · simp only [mul_assoc, Units.mul_inv_cancel_left]
    linear_combination -z.2 * (invOf_mul_self (2 : R))

end QuadraticAlgebra
