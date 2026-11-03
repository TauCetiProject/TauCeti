/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
public import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Contracting the combined coefficient of two coacted tensors

The diagonal coaction on a tensor product of comodules multiplies the coefficients of the two
factors (`TauCeti.Comodule.tensorCombine`). This file records how contracting the product
coefficient against a linear functional (`LinearMap.tensorComponent`) splits when the functional
splits on products, as a counit does, `ε (a * b) = ε a * ε b`, or a tangent vector at the
identity does, `d (a * b) = d a * ε b + ε a * d b`.

## Main results

* `TauCeti.Comodule.tensorComponent_tensorCombine`: contracting against a functional which splits
  on products as `θ (a * b) = φ a * ψ b + φ' a * ψ' b` splits the contraction accordingly.
* `TauCeti.Comodule.tensorComponent_mul`: the same splitting for the coefficient of a product in an
  algebra tensor product `A ⊗ C`, as for the coaction of a product in a comodule algebra.
-/

public section

open TensorProduct

namespace TauCeti.Comodule

variable {R C V W : Type*} [CommSemiring R]
variable [NonUnitalNonAssocSemiring C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Contracting the combined coefficient of two coacted tensors against a functional which splits
on products as `θ (a * b) = φ a * ψ b + φ' a * ψ' b` splits the contraction accordingly. -/
theorem tensorComponent_tensorCombine {θ φ ψ φ' ψ' : C →ₗ[R] R}
    (hθ : ∀ a b, θ (a * b) = φ a * ψ b + φ' a * ψ' b) (x : V ⊗[R] C) (y : W ⊗[R] C) :
    LinearMap.tensorComponent θ (tensorCombine (R := R) (C := C) (M := V) (N := W) (x ⊗ₜ y)) =
      LinearMap.tensorComponent φ x ⊗ₜ LinearMap.tensorComponent ψ y +
        LinearMap.tensorComponent φ' x ⊗ₜ LinearMap.tensorComponent ψ' y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [TensorProduct.add_tmul, map_add, hx, hx']
    abel
  | tmul v a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [TensorProduct.tmul_add, map_add, hy, hy']
      abel
    | tmul w b =>
      simp only [tensorCombine_tmul_tmul, LinearMap.tensorComponent_tmul, hθ, add_smul,
        TensorProduct.smul_tmul_smul]

/-- Contracting the coefficient of a product in an algebra tensor product `A ⊗ C` against a
functional which splits on products as `θ (a * b) = φ a * ψ b + φ' a * ψ' b` splits the
contraction accordingly. -/
theorem tensorComponent_mul {R A C : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring C] [Algebra R C] {θ φ ψ φ' ψ' : C →ₗ[R] R}
    (hθ : ∀ a b, θ (a * b) = φ a * ψ b + φ' a * ψ' b) (x y : A ⊗[R] C) :
    LinearMap.tensorComponent θ (x * y) =
      LinearMap.tensorComponent φ x * LinearMap.tensorComponent ψ y +
        LinearMap.tensorComponent φ' x * LinearMap.tensorComponent ψ' y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [add_mul, map_add, hx, hx']
    abel
  | tmul a c =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [mul_add, map_add, hy, hy']
      abel
    | tmul b c' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.tensorComponent_tmul, hθ,
        add_smul, smul_mul_smul_comm]

end TauCeti.Comodule
