/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Square-zero linear maps with coefficients in a commutative algebra

Let `f : M →ₗ[R] B` be a linear map into an `R`-algebra all of whose values square to zero, and
let `H` be a commutative `R`-algebra. Then the extension `f.rTensor H : M ⊗[R] H → B ⊗[R] H`
again has square-zero values. Commutativity of `H` is essential: the cross terms of
`(∑ f mᵢ ⊗ hᵢ) ^ 2` cancel in pairs because `f mᵢ * f mⱼ = -(f mⱼ * f mᵢ)` while
`hᵢ * hⱼ = hⱼ * hᵢ`. Neither unitality nor associativity is needed: `B` and `H` are only
assumed to be non-unital non-associative `R`-algebras.

This is exactly the hypothesis of `ExteriorAlgebra.lift`, so a linear map
`M →ₗ[R] M' ⊗[R] H` with coefficients in `H` followed by `ExteriorAlgebra.ι` extends to an
algebra homomorphism `ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M' ⊗[R] H`. The coaction of
the exterior algebra of a comodule over a commutative bialgebra is built this way.

## Main results

* `TauCeti.rTensor_mul_add_mul_swap_eq_zero`: tensor-extended values anticommute.
* `TauCeti.rTensor_mul_self_eq_zero`: square-zero values persist after tensoring with a
  commutative algebra on the right.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R M B H : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [NonUnitalNonAssocCommSemiring H] [Module R H] [SMulCommClass R H H] [IsScalarTower R H H]

/-- The cross terms of the square of a sum vanish: values of `f.rTensor H` anticommute. -/
theorem rTensor_mul_add_mul_swap_eq_zero {f : M →ₗ[R] B} (hf : ∀ m, f m * f m = 0)
    (x y : M ⊗[R] H) :
    f.rTensor H x * f.rTensor H y + f.rTensor H y * f.rTensor H x = 0 := by
  have hanti (m n : M) : f m * f n + f n * f m = 0 := by
    simpa [add_mul, mul_add, hf, add_comm] using hf (m + n)
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, add_mul, mul_add, add_add_add_comm, h₁, h₂, add_zero]
  | tmul m h =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, mul_add, add_mul, add_add_add_comm, h₁, h₂, add_zero]
    | tmul n k =>
      simp [mul_comm k h, ← TensorProduct.add_tmul, hanti]

/-- If every value of `f` squares to zero, so does every value of `f.rTensor H` for a
commutative algebra `H`. -/
theorem rTensor_mul_self_eq_zero {f : M →ₗ[R] B} (hf : ∀ m, f m * f m = 0) (x : M ⊗[R] H) :
    f.rTensor H x * f.rTensor H x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul m h => simp [hf]
  | add x y hx hy =>
    simp [add_mul, mul_add, hx, hy, rTensor_mul_add_mul_swap_eq_zero hf]

end TauCeti
