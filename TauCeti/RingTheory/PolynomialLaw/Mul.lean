/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Multiplicative
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Products of polynomial laws

For polynomial laws `f g : M →ₚₗ[R] B` with values in an `R`-algebra `B`, the pointwise
product `f * g`, computed after every scalar extension as `f(x) g(x)`, is again a polynomial law,
because base change of an algebra map is multiplicative. Degrees of homogeneity add, and products of
multiplicative laws on an algebra with values in a commutative algebra are multiplicative.

## Main declarations

* `PolynomialLaw.instMul`: the pointwise product of laws with values in an algebra, with
  `mul_toFun'`, `mul_toFun` and `ground_mul`.
* `PolynomialLaw.IsHomogeneousOfDegree.mul`: degrees of homogeneity add.
* `PolynomialLaw.IsMultiplicative.mul`: products of multiplicative laws are multiplicative.
-/

public section

noncomputable section

open TensorProduct

universe u

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {B : Type*} [Semiring B] [Algebra R B]

/-- The pointwise product of two polynomial laws with values in an algebra:
`(f * g)(x) = f(x) g(x)` after every scalar extension. -/
instance instMul : Mul (M →ₚₗ[R] B) where
  mul f g :=
    { toFun' S _ _ x := f.toFun' S x * g.toFun' S x
      isCompat' φ := funext fun x ↦ by
        rw [Function.comp_apply, Function.comp_apply, ← isCompat_apply', ← isCompat_apply',
          AlgHom.rTensor_toLinearMap_apply, AlgHom.rTensor_toLinearMap_apply,
          AlgHom.rTensor_toLinearMap_apply, map_mul] }

@[simp]
theorem mul_toFun' (f g : M →ₚₗ[R] B) (S : Type u) [CommSemiring S] [Algebra R S]
    (x : S ⊗[R] M) : (f * g).toFun' S x = f.toFun' S x * g.toFun' S x :=
  (rfl)

/-- The product of two laws evaluates as the product after scalar extension to a commutative
algebra in any universe. -/
@[simp]
theorem mul_toFun (f g : M →ₚₗ[R] B) (S : Type*) [CommSemiring S] [Algebra R S]
    (x : S ⊗[R] M) : (f * g).toFun S x = f.toFun S x * g.toFun S x := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective x
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, mul_toFun', AlgHom.rTensor_toLinearMap_apply, map_mul]

/-- The ground map of a product of laws is the product of the ground maps. -/
@[simp]
theorem ground_mul (f g : M →ₚₗ[R] B) (m : M) : (f * g).ground m = f.ground m * g.ground m := by
  simp only [ground_apply, mul_toFun', ← Algebra.TensorProduct.lid_toLinearEquiv,
    AlgEquiv.toLinearEquiv_apply, map_mul]

/-- Degrees of homogeneity add under products. -/
theorem IsHomogeneousOfDegree.mul {f g : M →ₚₗ[R] B} {p q : ℕ} (hf : f.IsHomogeneousOfDegree p)
    (hg : g.IsHomogeneousOfDegree q) : (f * g).IsHomogeneousOfDegree (p + q) :=
  isHomogeneousOfDegree_iff.mpr fun _ _ _ s x ↦ by
    rw [mul_toFun', mul_toFun', hf.toFun'_smul, hg.toFun'_smul, smul_mul_smul_comm, pow_add]

/-- Products of multiplicative laws on an algebra with values in a commutative algebra are
multiplicative. -/
theorem IsMultiplicative.mul {A : Type*} [Semiring A] [Algebra R A] {B : Type*} [CommSemiring B]
    [Algebra R B] {f g : A →ₚₗ[R] B}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : (f * g).IsMultiplicative where
  toFun'_one S _ _ := by rw [mul_toFun', hf.toFun'_one, hg.toFun'_one, one_mul]
  toFun'_mul x y := by
    rw [mul_toFun', mul_toFun', mul_toFun', hf.toFun'_mul, hg.toFun'_mul, mul_mul_mul_comm]

end PolynomialLaw
