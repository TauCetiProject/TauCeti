/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Tensor-product contractions and trace identities

This file defines contraction of a tensor product against a linear functional on its right factor,
and records its behavior on pure tensors and under tensor-product maps.
Such contractions extract coordinates and test tensor identities, supporting componentwise
arguments about coactions and weight spaces. It also proves the tensor identity that makes
the Casimir element of a trace commute with multiplication.

## Main declarations

* `LinearMap.tensorComponent`: contraction against the right factor of a tensor product.
* `LinearMap.tensorComponent_map`: naturality of contraction under `TensorProduct.map`.
* `LinearMap.tensorComponent_assoc_symm`: contraction commutes with reassociation.
* `LinearMap.comp_tensorComponent`: contraction commutes with a functional on the left.
* `TauCeti.tensorProduct_rid_rTensor_apply`: naturality of the right tensor unitor.
* `LinearMap.sum_mul_tmul_eq_sum_tmul_mul`: the Casimir element of a trace commutes with
  multiplication.

## References

* L. Kadison, *New examples of Frobenius extensions*, University Lecture Series 14, AMS, 1999
  (dual bases of Frobenius algebras and extensions, and their Casimir elements).
-/

public section

open TensorProduct
open scoped TensorProduct

namespace LinearMap

universe u v w x y

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Apply a linear functional to the right factor of a tensor. -/
noncomputable def tensorComponent (phi : N →ₗ[R] R) : M ⊗[R] N →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ phi.lTensor M

/-- Contraction is the tensor product of the functional with the identity, followed by the
right tensor unitor. -/
theorem tensorComponent_def (phi : N →ₗ[R] R) :
    tensorComponent (M := M) phi = (TensorProduct.rid R M).toLinearMap ∘ₗ phi.lTensor M := (rfl)

/-- A right tensor component sends a pure tensor to the corresponding scalar multiple. -/
@[simp]
theorem tensorComponent_tmul (phi : N →ₗ[R] R) (m : M) (n : N) :
    tensorComponent (R := R) (M := M) phi (m ⊗ₜ[R] n) = phi n • m := by
  simp [tensorComponent]

/-- Taking a right tensor component commutes with a map on both tensor factors. -/
@[simp]
theorem tensorComponent_map {M' : Type x} {N' : Type y}
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (phi : N' →ₗ[R] R) (f : M →ₗ[R] M') (g : N →ₗ[R] N') (t : M ⊗[R] N) :
    tensorComponent phi (TensorProduct.map f g t) =
      f (tensorComponent (phi.comp g) t) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp

/-- Contraction by the zero functional is the zero linear map. -/
@[simp]
theorem tensorComponent_zero :
    tensorComponent (R := R) (M := M) (0 : N →ₗ[R] R) = 0 := by
  refine TensorProduct.ext' fun m n => ?_
  simp

section

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Contraction of the last tensor factor commutes with reassociation. -/
@[simp]
theorem tensorComponent_assoc_symm (phi : P →ₗ[R] R) (u : M ⊗[R] (N ⊗[R] P)) :
    LinearMap.tensorComponent phi ((TensorProduct.assoc R M N P).symm u) =
      (LinearMap.tensorComponent phi).lTensor M u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul m v =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
    | tmul n p =>
      simp only [TensorProduct.assoc_symm_tmul, LinearMap.tensorComponent_tmul,
        LinearMap.lTensor_tmul, TensorProduct.tmul_smul]

/-- Applying functionals to both factors is independent of the order of contraction. -/
theorem comp_tensorComponent (psi : M →ₗ[R] R) (phi : N →ₗ[R] R) :
    psi ∘ₗ LinearMap.tensorComponent phi =
      phi ∘ₗ (TensorProduct.lid R N).toLinearMap ∘ₗ psi.rTensor N := by
  refine TensorProduct.ext' fun m n ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.tensorComponent_tmul, map_smul,
    smul_eq_mul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    mul_comm]

end

/-! ### The Casimir element of a trace

Let `φ : A →ₗ[k] k` be a trace on a `k`-algebra `A`, so `φ (a * b) = φ (b * a)`, and let `x` and
`y` be finite families dual to each other for the pairing `(a, b) ↦ φ (a * b)`, in the sense that
every element expands in either family with coefficients read off by pairing against the other:

```text
a = ∑ i, φ (a * y i) • x i,        a = ∑ i, φ (x i * a) • y i.
```

For a finite free symmetric Frobenius algebra, a basis and its dual basis give such families;
the expansion identities also allow redundant families. The **Casimir element** `∑ i, x i ⊗ y i`
of `A ⊗[k] A` then commutes with `A` in the bimodule sense:

```text
∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a).
```

This is what makes `1 ↦ ∑ i, x i ⊗ y i` a map of `A`-bimodules `A → A ⊗[k] A`, the coevaluation of
a symmetric Frobenius algebra; for a Frobenius coalgebra in Mathlib's sense
(`Coalgebra.IsFrobenius`) with counit `φ`, the element is the comultiplication of `1`.

The tensor identity itself needs only a `k`-module `A` with an associative multiplication.
No multiplicative identity, distributivity, or compatibility with scalar multiplication is needed.

-/

section Casimir

variable {k A : Type*} [CommSemiring k] [AddCommMonoid A] [Semigroup A] [Module k A]

/-- **The Casimir element of a trace commutes with multiplication.** If `φ` is a trace on `A`
and the finite families `x` and `y` are dual for `(a, b) ↦ φ (a * b)`, then
`∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a)` for every `a : A`. -/
theorem sum_mul_tmul_eq_sum_tmul_mul {ι : Type*} [Fintype ι] (φ : A →ₗ[k] k)
    (hφ : ∀ a b : A, φ (a * b) = φ (b * a)) {x y : ι → A}
    (hx : ∀ a : A, ∑ i, φ (a * y i) • x i = a) (hy : ∀ a : A, ∑ i, φ (x i * a) • y i = a)
    (a : A) :
    ∑ i, (a * x i) ⊗ₜ[k] y i = ∑ i, x i ⊗ₜ[k] (y i * a) := by
  -- Expand each `a * x i` in the family `x`; the coefficients then match those of the expansion
  -- of `y j * a` in the family `y`, by the trace property.
  have expand (i : ι) :
      (a * x i) ⊗ₜ[k] y i = ∑ j, x j ⊗ₜ[k] (φ (x i * (y j * a)) • y i) := by
    conv_lhs => rw [← hx (a * x i)]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul, mul_assoc, hφ, mul_assoc]
  simp_rw [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.tmul_sum, hy]

end Casimir

end LinearMap

namespace TauCeti

variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The right tensor unitor is natural with respect to a linear map in its left factor. -/
@[simp]
theorem tensorProduct_rid_rTensor_apply (f : M →ₗ[R] N) (t : M ⊗[R] R) :
    TensorProduct.rid R N (LinearMap.rTensor R f t) = f (TensorProduct.rid R M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m r => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

end TauCeti
