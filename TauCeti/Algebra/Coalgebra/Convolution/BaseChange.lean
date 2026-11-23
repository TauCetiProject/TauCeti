/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Convolution over a base-changed coalgebra

Let `C` be a coalgebra over `R` and `S` a commutative `R`-algebra, so that `S ⊗[R] C` is a
coalgebra over `S` with `Δ (1 ⊗ c) = ∑ (1 ⊗ c₁) ⊗ (1 ⊗ c₂)`. Restricting `S`-linear maps out of
`S ⊗[R] C` along `c ↦ 1 ⊗ c` therefore turns their convolution product into the convolution
product over `C` of the restrictions.

The statement reads the values through a ring homomorphism `ψ`, so that the two convolution
algebras may use different copies of the value ring, for instance type synonyms carrying
different module structures.

## Main results

* `LinearMap.map_convMul_apply_one_tmul`: restriction along `c ↦ 1 ⊗ c` is multiplicative for
  convolution.
-/

public section

open scoped TensorProduct
open WithConv

namespace LinearMap

variable {R S C B₁ B₂ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [Semiring B₁] [Algebra S B₁] [Semiring B₂] [Algebra R B₂]

/-- **Convolution commutes with restriction along `c ↦ 1 ⊗ c`.** If `ψ` carries the values of
`F₁` and `F₂` on `1 ⊗ c` to those of `G₁` and `G₂` on `c`, it carries the value of the
convolution `F₁ * F₂` on `1 ⊗ c` to that of `G₁ * G₂` on `c`. -/
theorem map_convMul_apply_one_tmul (ψ : B₁ →+* B₂)
    (F₁ F₂ : WithConv (S ⊗[R] C →ₗ[S] B₁)) (G₁ G₂ : WithConv (C →ₗ[R] B₂))
    (h₁ : ∀ c, ψ (F₁ (1 ⊗ₜ c)) = G₁ c) (h₂ : ∀ c, ψ (F₂ (1 ⊗ₜ c)) = G₂ c) (c : C) :
    ψ ((F₁ * F₂) (1 ⊗ₜ c)) = (G₁ * G₂) c := by
  rw [convMul_apply, convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) c using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul a b => simp [h₁, h₂]

end LinearMap
