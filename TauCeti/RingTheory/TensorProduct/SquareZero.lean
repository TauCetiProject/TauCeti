/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Square-zero linear maps with coefficients in a commutative algebra

Let `B` be a non-unital non-associative `R`-algebra, let `f : M →ₗ[R] B` be a linear map all
of whose values square to zero, and let `H` be a commutative non-unital non-associative
`R`-algebra. Then the extension `f.rTensor H : M ⊗[R] H → B ⊗[R] H` again has square-zero
values. Expanding `f (m + n) * f (m + n) = 0` gives `f m * f n + f n * f m = 0`, so for pure
tensors the cross terms satisfy
`(f m ⊗ h) * (f n ⊗ k) + (f n ⊗ k) * (f m ⊗ h) = (f m * f n + f n * f m) ⊗ (h * k) = 0`.
This uses `k * h = h * k`, which is why commutativity of `H` is assumed. Neither unitality,
associativity nor additive inverses are needed in `B` or `H`.

In the unital associative case `[CommSemiring H] [Algebra R H]`, with `B = ExteriorAlgebra R M'`,
this supplies the hypothesis of `ExteriorAlgebra.lift`. A linear map `g : M →ₗ[R] M' ⊗[R] H`
followed by `(ExteriorAlgebra.ι R).rTensor H` therefore extends to an algebra homomorphism
`ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M' ⊗[R] H`. The coaction of the exterior algebra
of a comodule over a commutative bialgebra is built this way.

## Main results

* `TauCeti.rTensor_mul_add_mul_swap_eq_zero`: for values `a, b` of `f.rTensor H`,
  `a * b + b * a = 0`.
* `TauCeti.rTensor_mul_self_eq_zero`: square-zero values persist after tensoring on the right
  with a commutative non-unital non-associative algebra.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R M B H : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [NonUnitalNonAssocCommSemiring H] [Module R H] [SMulCommClass R H H] [IsScalarTower R H H]

/-- If every value of `f` squares to zero, then any two values `a, b` of `f.rTensor H` satisfy
`a * b + b * a = 0`: the cross terms of the square of a sum vanish. -/
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

/-- If every value of `f` squares to zero, so does every value of `f.rTensor H`, for `H` a
commutative non-unital non-associative `R`-algebra. -/
theorem rTensor_mul_self_eq_zero {f : M →ₗ[R] B} (hf : ∀ m, f m * f m = 0) (x : M ⊗[R] H) :
    f.rTensor H x * f.rTensor H x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul m h => simp [hf]
  | add x y hx hy =>
    simp [add_mul, mul_add, hx, hy, rTensor_mul_add_mul_swap_eq_zero hf]

end TauCeti
