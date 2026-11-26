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

Likewise, two non-unital star algebra homomorphisms `f : A → C` and `g : B → D` induce a
non-unital star algebra homomorphism `A ⊗[R] B → C ⊗[R] D`, `a ⊗ b ↦ f a ⊗ g b`: the non-unital
star version of Mathlib's `Algebra.TensorProduct.map`.

## Main declarations

* `Algebra.TensorProduct.liftNonUnitalStarAlgHom`: the star homomorphism `a ⊗ b ↦ φ a * ψ b`.
* `Algebra.TensorProduct.mapNonUnitalStarAlgHom`: the star homomorphism `a ⊗ b ↦ f a ⊗ g b`,
  with `Algebra.TensorProduct.mapNonUnitalStarAlgHom_id` and
  `Algebra.TensorProduct.mapNonUnitalStarAlgHom_comp`.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

section Lift

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

end Lift

section Map

variable {R A B C D : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [StarRing A] [NonUnitalSemiring B] [Module R B] [StarRing B]
  [NonUnitalSemiring C] [Module R C] [StarRing C] [NonUnitalSemiring D] [Module R D] [StarRing D]
  (f : A →⋆ₙₐ[R] C) (g : B →⋆ₙₐ[R] D)

private theorem map_mul_of_nonUnitalStarAlgHom
    [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass R B B] [IsScalarTower R B B]
    [SMulCommClass R C C] [IsScalarTower R C C] [SMulCommClass R D D] [IsScalarTower R D D]
    (x y : A ⊗[R] B) :
    TensorProduct.map (f : A →ₗ[R] C) (g : B →ₗ[R] D) (x * y) =
      TensorProduct.map (f : A →ₗ[R] C) (g : B →ₗ[R] D) x *
        TensorProduct.map (f : A →ₗ[R] C) (g : B →ₗ[R] D) y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | tmul a' b' => simp [tmul_mul_tmul]

private theorem map_star_of_nonUnitalStarAlgHom [StarRing R] [StarModule R A] [StarModule R B]
    [StarModule R C] [StarModule R D] (x : A ⊗[R] B) :
    TensorProduct.map (f : A →ₗ[R] C) (g : B →ₗ[R] D) (star x) =
      star (TensorProduct.map (f : A →ₗ[R] C) (g : B →ₗ[R] D) x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [star_add, map_add, hx, hx']
  | tmul a b => simp [map_star]

variable [SMulCommClass R A A] [IsScalarTower R A A] [SMulCommClass R B B] [IsScalarTower R B B]
  [SMulCommClass R C C] [IsScalarTower R C C] [SMulCommClass R D D] [IsScalarTower R D D]
  [StarRing R] [StarModule R A] [StarModule R B] [StarModule R C] [StarModule R D]

/-- **The tensor product of star homomorphisms**: the non-unital star algebra homomorphism
`A ⊗[R] B → C ⊗[R] D`, `a ⊗ b ↦ f a ⊗ g b`. This is the non-unital star version of Mathlib's
`Algebra.TensorProduct.map`, which takes unital algebra homomorphisms. -/
noncomputable def mapNonUnitalStarAlgHom : A ⊗[R] B →⋆ₙₐ[R] C ⊗[R] D where
  __ := TensorProduct.map (f : A →ₗ[R] C) (g : B →ₗ[R] D)
  map_zero' := map_zero _
  map_mul' := map_mul_of_nonUnitalStarAlgHom f g
  map_star' := map_star_of_nonUnitalStarAlgHom f g

@[simp]
theorem mapNonUnitalStarAlgHom_tmul (a : A) (b : B) :
    mapNonUnitalStarAlgHom f g (a ⊗ₜ b) = f a ⊗ₜ g b :=
  (rfl)

/-- The underlying function of `mapNonUnitalStarAlgHom f g` is `TensorProduct.map f g`. -/
theorem coe_mapNonUnitalStarAlgHom :
    ⇑(mapNonUnitalStarAlgHom f g) = TensorProduct.map (f : A →ₗ[R] C) (g : B →ₗ[R] D) :=
  (rfl)

/-- The tensor product of the identities is the identity. -/
@[simp]
theorem mapNonUnitalStarAlgHom_id :
    mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.id R A) (NonUnitalStarAlgHom.id R B) =
      NonUnitalStarAlgHom.id R (A ⊗[R] B) :=
  NonUnitalStarAlgHom.ext fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a b => simp only [mapNonUnitalStarAlgHom_tmul, NonUnitalStarAlgHom.coe_id, id_eq]

/-- The tensor product of composites is the composite of the tensor products. -/
theorem mapNonUnitalStarAlgHom_comp {C' D' : Type*} [NonUnitalSemiring C'] [Module R C']
    [StarRing C'] [NonUnitalSemiring D'] [Module R D'] [StarRing D'] [SMulCommClass R C' C']
    [IsScalarTower R C' C'] [SMulCommClass R D' D'] [IsScalarTower R D' D'] [StarModule R C']
    [StarModule R D'] (f' : C →⋆ₙₐ[R] C') (g' : D →⋆ₙₐ[R] D') :
    mapNonUnitalStarAlgHom (f'.comp f) (g'.comp g) =
      (mapNonUnitalStarAlgHom f' g').comp (mapNonUnitalStarAlgHom f g) :=
  NonUnitalStarAlgHom.ext fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a b => simp

end Map

end Algebra.TensorProduct
