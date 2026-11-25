/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Lifting commuting star homomorphisms to a tensor product

Let `A`, `B` and `C` be possibly nonunital star algebras over a commutative star ring `R`. Two
non-unital star algebra homomorphisms `φ : A → C` and `ψ : B → C` whose values commute,
`φ a * ψ b = ψ b * φ a`, combine to a non-unital star algebra homomorphism
`A ⊗[R] B → C`, `a ⊗ b ↦ φ a * ψ b`. This is the non-unital star version of Mathlib's
`Algebra.TensorProduct.lift`, which takes unital algebra homomorphisms.

## Main declarations

* `Algebra.TensorProduct.liftNonUnitalStarAlgHom`: the star homomorphism `a ⊗ b ↦ φ a * ψ b`.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B C : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [StarRing A] [NonUnitalSemiring B] [Module R B] [StarRing B]
  [NonUnitalSemiring C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C] [StarRing C]
  (φ : A →⋆ₙₐ[R] C) (ψ : B →⋆ₙₐ[R] C)

/-- The linear map `a ⊗ b ↦ φ a * ψ b` underlying `liftNonUnitalStarAlgHom`. -/
private noncomputable def liftLinear : A ⊗[R] B →ₗ[R] C :=
  TensorProduct.lift <| (LinearMap.mul R C).compl₁₂ (φ : A →ₗ[R] C) (ψ : B →ₗ[R] C)

private theorem liftLinear_tmul (a : A) (b : B) : liftLinear φ ψ (a ⊗ₜ b) = φ a * ψ b :=
  (rfl)

variable {φ ψ}

private theorem liftLinear_star [StarRing R] [StarModule R A] [StarModule R B]
    (h : ∀ a b, Commute (φ a) (ψ b)) (x : A ⊗[R] B) :
    liftLinear φ ψ (star x) = star (liftLinear φ ψ x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [star_add, hx, hx']
  | tmul a b =>
    rw [TensorProduct.star_tmul, liftLinear_tmul, liftLinear_tmul, star_mul, ← map_star,
      ← map_star, (h _ _).eq]

variable [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass R B B] [IsScalarTower R B B]

private theorem liftLinear_mul (h : ∀ a b, Commute (φ a) (ψ b)) (x y : A ⊗[R] B) :
    liftLinear φ ψ (x * y) = liftLinear φ ψ x * liftLinear φ ψ y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [add_mul, hx, hx']
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp [mul_add, hy, hy']
    | tmul a' b' =>
      rw [tmul_mul_tmul, liftLinear_tmul, liftLinear_tmul, liftLinear_tmul, map_mul, map_mul,
        (h a' b).mul_mul_mul_comm]

variable [StarRing R] [StarModule R A] [StarModule R B]

variable (φ ψ) in
/-- **The tensor product of commuting star homomorphisms**: the non-unital star algebra
homomorphism `A ⊗[R] B → C`, `a ⊗ b ↦ φ a * ψ b`, for `φ` and `ψ` with commuting values. -/
noncomputable def liftNonUnitalStarAlgHom (h : ∀ a b, Commute (φ a) (ψ b)) :
    A ⊗[R] B →⋆ₙₐ[R] C where
  __ := liftLinear φ ψ
  map_zero' := map_zero _
  map_mul' := liftLinear_mul h
  map_star' := liftLinear_star h

@[simp]
theorem liftNonUnitalStarAlgHom_tmul (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    liftNonUnitalStarAlgHom φ ψ h (a ⊗ₜ b) = φ a * ψ b :=
  (rfl)

end Algebra.TensorProduct
