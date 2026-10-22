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
bundled as a linear map in the functional, and records its behavior on pure tensors and under
tensor-product maps.
Such contractions extract coordinates and test tensor identities, supporting componentwise
arguments about coactions and weight spaces.
It records naturality identities for the associator that arise when manipulating
coassociativity of coactions.
It also proves the tensor identity that makes the Casimir element of a trace commute with
multiplication.

## Main declarations

* `LinearMap.tensorComponent`: contraction against the right factor of a tensor product.
* `LinearMap.tensorComponent_map`: naturality of contraction under `TensorProduct.map`.
* `LinearMap.tensorComponent_assoc_symm`: contraction commutes with reassociation.
* `LinearMap.comp_tensorComponent`: contraction commutes with a functional on the left.
* `LinearMap.lTensor_comp_map_id_comm`: maps on separate tensor factors commute.
* `LinearMap.tensorComponent_comp_tensorComponent`: successive contractions combine after
  reassociation.
* `LinearMap.lTensor_map_assoc_rTensor_natural`, `LinearMap.lTensor_assoc_rTensor_natural`,
  `LinearMap.assoc_rTensor_lTensor_natural`: reassociation after expanding the left factor is
  natural in maps on the other factors.
* `LinearMap.assoc_flip_mk_rTensor`: inserting a fixed middle factor commutes with
  reassociation.
* `LinearMap.rid_rTensor_apply`: naturality of the right tensor unitor.
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

/-- Applying a linear map to the right tensor factor commutes with applying one to the left
factor. -/
theorem lTensor_comp_map_id_comm {P : Type x} {Q : Type y}
    [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
    (f : M →ₗ[R] N) (g : P →ₗ[R] Q) :
    TensorProduct.map LinearMap.id g ∘ₗ TensorProduct.map f LinearMap.id =
      TensorProduct.map f LinearMap.id ∘ₗ TensorProduct.map LinearMap.id g := by
  apply LinearMap.ext
  intro t
  induction t with
  | tmul m p => simp
  | add x y hx hy =>
      simpa only [LinearMap.comp_apply, map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- Apply a linear functional to the right factor of a tensor, linearly in the functional. -/
noncomputable def tensorComponent : (N →ₗ[R] R) →ₗ[R] M ⊗[R] N →ₗ[R] M :=
  (LinearMap.compRight R (TensorProduct.rid R M).toLinearMap).comp (LinearMap.lTensorHom M)

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

/-- Applying two tensor components successively is contraction by the composed functional
on the last two factors, after reassociation. -/
theorem tensorComponent_comp_tensorComponent (phi : N →ₗ[R] R) (psi : P →ₗ[R] R) :
    tensorComponent (M := M) phi ∘ₗ tensorComponent (M := M ⊗[R] N) psi =
      tensorComponent (M := M) (phi ∘ₗ tensorComponent psi) ∘ₗ
        (TensorProduct.assoc R M N P).toLinearMap := by
  refine TensorProduct.ext_threefold fun m n p ↦ ?_
  simp [smul_smul]

/-- Applying functionals to both factors is independent of the order of contraction. -/
theorem comp_tensorComponent (psi : M →ₗ[R] R) (phi : N →ₗ[R] R) :
    psi ∘ₗ LinearMap.tensorComponent phi =
      phi ∘ₗ (TensorProduct.lid R N).toLinearMap ∘ₗ psi.rTensor N := by
  refine TensorProduct.ext' fun m n ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.tensorComponent_tmul, map_smul,
    smul_eq_mul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    mul_comm]

end

section AssocNatural

variable {R M N P P' S S' : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [AddCommMonoid P'] [Module R P']
  [AddCommMonoid S] [Module R S] [AddCommMonoid S'] [Module R S']

/-- Reassociating after expanding the left factor by `ρ : M → N ⊗ P` is natural in maps on the
last two factors. -/
theorem lTensor_map_assoc_rTensor_natural (f : P →ₗ[R] P') (g : S →ₗ[R] S')
    (ρ : M →ₗ[R] N ⊗[R] P) (t : M ⊗[R] S) :
    (TensorProduct.map f g).lTensor N (TensorProduct.assoc R N P S (ρ.rTensor S t)) =
      TensorProduct.assoc R N P' S' ((f.lTensor N ∘ₗ ρ).rTensor S' (g.lTensor M t)) := by
  induction t with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m s =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply]
    induction ρ m with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul n p => simp

/-- Reassociating after expanding the left factor by `ρ : M → N ⊗ P` is natural in a map on the
last factor. -/
theorem lTensor_assoc_rTensor_natural (π : S →ₗ[R] S') (ρ : M →ₗ[R] N ⊗[R] P)
    (t : M ⊗[R] S) :
    (π.lTensor P).lTensor N (TensorProduct.assoc R N P S (ρ.rTensor S t)) =
      TensorProduct.assoc R N P S' (ρ.rTensor S' (π.lTensor M t)) := by
  have h := lTensor_map_assoc_rTensor_natural LinearMap.id π ρ t
  rw [LinearMap.lTensor_id, LinearMap.id_comp] at h
  -- `π.lTensor P` is `TensorProduct.map LinearMap.id π` by definition.
  exact h

/-- Reassociating after expanding the left factor by `ρ : M → N ⊗ P` is natural in a map on the
middle factor. -/
theorem assoc_rTensor_lTensor_natural (π : P →ₗ[R] P') (ρ : M →ₗ[R] N ⊗[R] P)
    (t : M ⊗[R] S) :
    TensorProduct.assoc R N P' S ((π.lTensor N ∘ₗ ρ).rTensor S t) =
      (π.rTensor S).lTensor N (TensorProduct.assoc R N P S (ρ.rTensor S t)) := by
  rw [LinearMap.rTensor_comp_apply]
  exact (LinearMap.congr_fun
    (LinearMap.lTensor_rTensor_comp_assoc (M := P) (N := P') (P := N) (Q := S) π)
    (ρ.rTensor S t)).symm

/-- Inserting a fixed vector `p` as a new middle tensor factor commutes with reassociation. -/
theorem assoc_flip_mk_rTensor (p : P) (y : M ⊗[R] S) :
    TensorProduct.assoc R M P S (((TensorProduct.mk R M P).flip p).rTensor S y) =
      (TensorProduct.mk R P S p).lTensor M y := by
  induction y with
  | tmul a b => simp
  | add y z hy hz => simp [hy, hz]

end AssocNatural

/-- The right tensor unitor is natural with respect to a linear map in its left factor. -/
@[simp]
theorem rid_rTensor_apply (f : M →ₗ[R] N) (t : M ⊗[R] R) :
    TensorProduct.rid R N (rTensor R f t) = f (TensorProduct.rid R M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m r => simp
  | add x y hx hy => simp only [map_add, hx, hy]

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
