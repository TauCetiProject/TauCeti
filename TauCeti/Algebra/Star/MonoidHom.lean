/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.Algebra.Star.StarAlgHom
public import TauCeti.Algebra.Ring.Hom

/-!
# Corner unitization of non-unital `⋆`-algebra homomorphisms as `⋆`-monoid homomorphisms

Given a possibly non-unital `⋆`-algebra homomorphism `ρ : A →⋆ₙₐ[R] B` from a unital `⋆`-semiring
`A` into a unital `⋆`-ring `B`, the image `ρ 1` is an idempotent self-adjoint element and
`a ↦ ρ a + (1 - ρ 1)` extends `ρ` by the identity on the complementary corner `1 - ρ 1` to a
`StarMonoidHom` `A →⋆* B` (`NonUnitalStarAlgHom.unitizeStarMonoidHom`), built on `MulHom.unitize`.
Composing with `Unitary.map` pushes unitaries of `A` to unitaries of `B` whose conjugation action on
`ρ b` sends `ρ b` to `ρ (u * b * star u)`
(`NonUnitalStarAlgHom.unitizeStarMonoidHom_mul_apply_mul_star`).

## Main definitions and results

* `NonUnitalStarAlgHom.unitizeStarMonoidHom`: the `⋆`-monoid homomorphism `a ↦ ρ a + (1 - ρ 1)`.
* `NonUnitalStarAlgHom.toMonoidHom_unitizeStarMonoidHom`: forgetting `star` identifies
  `ρ.unitizeStarMonoidHom` with `MulHom.unitize`.
* `NonUnitalStarAlgHom.unitizeStarMonoidHom_mul_apply` and
  `NonUnitalStarAlgHom.apply_mul_unitizeStarMonoidHom`: absorption against `ρ b` on either side.
* `NonUnitalStarAlgHom.unitizeStarMonoidHom_mul_apply_mul_star`: conjugation of `ρ b` by
  `ρ.unitizeStarMonoidHom a` equals `ρ (a * b * star a)`.

## References

* M. Rørdam, *Classification of Nuclear C⋆-Algebras*, Encyclopaedia of Mathematical Sciences 126,
  Springer (2002), §2.1.
-/

public section

namespace NonUnitalStarAlgHom

variable {R A B : Type*} [Monoid R]
  [Semiring A] [DistribMulAction R A] [StarMul A]
  [Ring B] [DistribMulAction R B] [StarRing B]

/-- Extend a possibly non-unital `⋆`-algebra homomorphism `ρ : A →⋆ₙₐ[R] B` between unital
`⋆`-rings to a `StarMonoidHom` `A →⋆* B` via `a ↦ ρ a + (1 - ρ 1)`, acting as the identity on the
complementary corner `1 - ρ 1` so that `Unitary.map` sends unitaries of `A` to unitaries of `B`. -/
def unitizeStarMonoidHom (ρ : A →⋆ₙₐ[R] B) : A →⋆* B where
  toMonoidHom := MulHom.unitize (ρ : A →ₙ* B)
  map_star' a := by
    change (MulHom.unitize (ρ : A →ₙ* B)) (star a) = star ((MulHom.unitize (ρ : A →ₙ* B)) a)
    simp only [MulHom.unitize_apply, MulHom.coe_coe, star_add, star_sub, star_one, ← map_star]

/-- Forgetting `star` identifies `ρ.unitizeStarMonoidHom` with `MulHom.unitize`. -/
@[simp]
theorem toMonoidHom_unitizeStarMonoidHom (ρ : A →⋆ₙₐ[R] B) :
    ρ.unitizeStarMonoidHom.toMonoidHom = MulHom.unitize (ρ : A →ₙ* B) := by
  rfl

/-- Explicit formula `ρ.unitizeStarMonoidHom a = ρ a + (1 - ρ 1)`. -/
theorem unitizeStarMonoidHom_apply (ρ : A →⋆ₙₐ[R] B) (a : A) :
    ρ.unitizeStarMonoidHom a = ρ a + (1 - ρ 1) := by
  rw [← StarMonoidHom.coe_toMonoidHom, toMonoidHom_unitizeStarMonoidHom, MulHom.unitize_apply]
  rfl

/-- When `ρ 1 = 1`, `ρ.unitizeStarMonoidHom` agrees pointwise with `ρ`. -/
theorem unitizeStarMonoidHom_apply_of_map_one {ρ : A →⋆ₙₐ[R] B} (hρ : ρ 1 = 1) (a : A) :
    ρ.unitizeStarMonoidHom a = ρ a := by
  rw [unitizeStarMonoidHom_apply, hρ, sub_self, add_zero]

/-- Left multiplication by `ρ.unitizeStarMonoidHom a` on `ρ b` drops the complementary corner
`1 - ρ 1`. -/
@[simp]
theorem unitizeStarMonoidHom_mul_apply (ρ : A →⋆ₙₐ[R] B) (a b : A) :
    ρ.unitizeStarMonoidHom a * ρ b = ρ (a * b) := by
  rw [unitizeStarMonoidHom_apply, add_mul, TauCeti.one_sub_map_one_mul_apply, add_zero, ← map_mul]

/-- Right multiplication by `ρ.unitizeStarMonoidHom b` on `ρ a` drops the complementary corner
`1 - ρ 1`. -/
@[simp]
theorem apply_mul_unitizeStarMonoidHom (ρ : A →⋆ₙₐ[R] B) (a b : A) :
    ρ a * ρ.unitizeStarMonoidHom b = ρ (a * b) := by
  rw [unitizeStarMonoidHom_apply, mul_add, TauCeti.apply_mul_one_sub_map_one, add_zero, ← map_mul]

/-- Conjugating `ρ b` by `ρ.unitizeStarMonoidHom a` coincides with applying `ρ` to `a * b * star a`.
-/
theorem unitizeStarMonoidHom_mul_apply_mul_star (ρ : A →⋆ₙₐ[R] B) (a b : A) :
    ρ.unitizeStarMonoidHom a * ρ b * star (ρ.unitizeStarMonoidHom a) = ρ (a * b * star a) := by
  rw [unitizeStarMonoidHom_mul_apply, ← map_star, apply_mul_unitizeStarMonoidHom, mul_assoc]

end NonUnitalStarAlgHom
