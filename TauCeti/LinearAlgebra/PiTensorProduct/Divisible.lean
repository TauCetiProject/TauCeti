/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import TauCeti.LinearAlgebra.TensorProduct.Divisible
import TauCeti.Algebra.Module.LinearMap.End

/-!
# Divisibility in multiple tensor products

Let `R` be a commutative ring, `r : R`, and `M : ι → Type*` a family of `R`-modules. This file
shows:

* if multiplication by `r` is surjective on one factor `M i₀`, it is surjective on
  `⨂[R] i, M i`;
* if multiplication by `r` is surjective on two distinct factors `M i₀` and `M i₁`, it is
  bijective on `⨂[R] i, M i`, whether or not the factors have `r`-torsion.

The second statement reduces to the case of two factors through the splitting
`⨂[R] i, M i ≃ (⨂[R] i : {i₀}ᶜ, M i) ⊗[R] M i₀`. For `R = ℤ` and the constant family on the
multiplicative group of an algebraically closed field, it says that the tensor powers
`⨂[ℤ]^n (Additive Fˣ)` are uniquely divisible for `n ≥ 2`. Degree one is genuinely excluded:
`Additive Fˣ` itself is divisible but has torsion, the roots of unity.

## Main results

* `PiTensorProduct.surjective_smul_of_surjective`: one `r`-divisible factor makes the tensor
  product `r`-divisible.
* `PiTensorProduct.isSMulRegular_of_surjective_smul`: two `r`-divisible factors make
  multiplication by `r` injective on the tensor product.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Proposition 6.4.1 and Exercise 7.3.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R ι : Type*} {M : ι → Type*} {r : R}

/-- If multiplication by `r` is surjective on one factor `M i₀`, it is surjective on the tensor
product `⨂[R] i, M i`. -/
theorem surjective_smul_of_surjective [CommSemiring R] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i₀ : ι) (h : Function.Surjective fun m : M i₀ ↦ r • m) :
    Function.Surjective fun x : ⨂[R] i, M i ↦ r • x := by
  classical
  suffices hrange : LinearMap.range (DistribSMul.toLinearMap R (⨂[R] i, M i) r) = ⊤ by
    rw [← DistribSMul.coe_toLinearMap R]
    exact LinearMap.range_eq_top.1 hrange
  rw [eq_top_iff, ← span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  obtain ⟨m, hm : r • m = f i₀⟩ := h (f i₀)
  refine ⟨tprod R (Function.update f i₀ m), ?_⟩
  have key := (tprod R).map_update_smul f i₀ r m
  rw [hm, Function.update_eq_self, RingHom.id_apply] at key
  rw [DistribSMul.toLinearMap_apply, ← key]

/-- If multiplication by `r` is surjective on two distinct factors `M i₀` and `M i₁`, it is
injective on the tensor product `⨂[R] i, M i`. Together with
`PiTensorProduct.surjective_smul_of_surjective`, multiplication by `r` is then bijective. -/
theorem isSMulRegular_of_surjective_smul [CommRing R] [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] {i₀ i₁ : ι} (h : i₀ ≠ i₁)
    (h₀ : Function.Surjective fun m : M i₀ ↦ r • m)
    (h₁ : Function.Surjective fun m : M i₁ ↦ r • m) :
    IsSMulRegular (⨂[R] i, M i) r := by
  classical
  exact ((equivPiTensorComplSingletonTensor R M i₀).isSMulRegular_congr r).2 <|
    TensorProduct.isSMulRegular_of_surjective_smul
      (surjective_smul_of_surjective (M := fun i : ({i₀}ᶜ : Set ι) ↦ M i) ⟨i₁, h.symm⟩ h₁) h₀

end PiTensorProduct
