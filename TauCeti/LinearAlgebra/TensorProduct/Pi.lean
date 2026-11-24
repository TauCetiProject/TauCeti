/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi

import Mathlib.Algebra.FiveLemma
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.Algebra.Exact.Pi

/-!
# Tensoring a finitely presented module with an arbitrary product

For an `R`-module `N` and a family of `R`-modules `(M i)`, Mathlib's comparison map
`TensorProduct.piRightHom : N ⊗[R] (∀ i, M i) → ∀ i, N ⊗[R] M i`, `n ⊗ m ↦ (n ⊗ m i)ᵢ`, is an
isomorphism when the index type is finite (`TensorProduct.piRight`). This file shows that it is an
isomorphism for an *arbitrary* index type as soon as `N` is finitely presented.

The comparison map is natural in `N` (`TensorProduct.piRightHom_comp_rTensor`). For `N = R ^ n`
both sides are `n`-fold products of the factors, and a finite presentation
`R ^ m → R ^ n → N → 0` stays right exact after tensoring with the product and after taking the
product of the tensored sequences, so the five lemma gives the general case. Finite presentation
cannot be weakened to finite generation in general; this is why Chase's theorem, that arbitrary
products of flat modules are flat, holds over coherent rings, where finitely generated ideals are
finitely presented.

## Main results

* `TensorProduct.piRightHom_comp_rTensor`: naturality of `TensorProduct.piRightHom` in the
  left factor.
* `TensorProduct.piRightHom_bijective_of_finitePresentation`: tensoring with a finitely presented
  module commutes with arbitrary products.
* `TensorProduct.piScalarRight_tmul_eq_smul`: for a commutative `R`-algebra `A`, the
  identification `A ⊗[R] (ι → R) ≃ (ι → A)` sends `a ⊗ v` to `a` times `v` with coordinates
  mapped into `A`.

## References

* S. U. Chase, *Direct products of modules*, Trans. Amer. Math. Soc. 97 (1960), §2.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {R : Type*} {ι : Type*} {M : ι → Type*}

section CommSemiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N N' : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']

/-- The comparison map `N ⊗[R] (∀ i, M i) → ∀ i, N ⊗[R] M i` is natural in `N`. -/
theorem piRightHom_comp_rTensor (f : N →ₗ[R] N') :
    piRightHom R R N' M ∘ₗ f.rTensor (∀ i, M i) =
      LinearMap.piMap (fun i ↦ f.rTensor (M i)) ∘ₗ piRightHom R R N M :=
  TensorProduct.ext' fun _ _ ↦ rfl

end CommSemiring

section PiScalarRight

variable {A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Fintype ι] [DecidableEq ι]

/-- Read on `ι → A`, the pure tensor `a ⊗ v` is `a` times the vector `v` with coordinates mapped
into `A`. -/
theorem piScalarRight_tmul_eq_smul (a : A) (v : ι → R) :
    piScalarRight R A A ι (a ⊗ₜ v) = a • fun i ↦ algebraMap R A (v i) := by
  ext i
  simp [_root_.Algebra.smul_def, mul_comm]

end PiScalarRight

section CommRing

variable [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

variable (R M) in
/-- Tensoring with a finite free module commutes with arbitrary products: both sides of the
comparison map are `κ`-fold products of the factors. -/
private theorem piRightHom_bijective_of_finite_free (κ : Type*) [Finite κ] :
    Function.Bijective (piRightHom R R (κ → R) M) := by
  classical
  have := Fintype.ofFinite κ
  let e₁ : (κ → R) ⊗[R] (∀ i, M i) ≃ₗ[R] κ → ∀ i, M i :=
    TensorProduct.comm R _ _ ≪≫ₗ piScalarRight R R (∀ i, M i) κ
  let e₂ : (∀ i, (κ → R) ⊗[R] M i) ≃ₗ[R] ∀ i, κ → M i :=
    LinearEquiv.piCongrRight fun i ↦ TensorProduct.comm R _ _ ≪≫ₗ piScalarRight R R (M i) κ
  let e₃ : (κ → ∀ i, M i) ≃ₗ[R] ∀ i, κ → M i :=
    { Equiv.piComm fun (_ : κ) i ↦ M i with
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have h : e₂.toLinearMap ∘ₗ piRightHom R R (κ → R) M = (e₁ ≪≫ₗ e₃).toLinearMap :=
    TensorProduct.ext' fun x m ↦ by
      ext i k
      simp [e₁, e₂, e₃, Equiv.piComm, Function.swap]
  rw [← e₂.bijective.of_comp_iff', ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, h]
  exact LinearEquiv.bijective _

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- **Tensoring with a finitely presented module commutes with arbitrary products**: for `N`
finitely presented, `N ⊗[R] (∀ i, M i) → ∀ i, N ⊗[R] M i` is bijective for every index type,
finite or not. -/
theorem piRightHom_bijective_of_finitePresentation (S : Type*) [CommSemiring S] [Algebra R S]
    [Module S N] [IsScalarTower R S N] [Module.FinitePresentation R N] :
    Function.Bijective (piRightHom R S N M) := by
  -- `piRightHom` is `S`-linear only for bookkeeping: as a function it is the `R`-linear one.
  have hS : ⇑(piRightHom R S N M) = piRightHom R R N M :=
    congrArg DFunLike.coe (TensorProduct.ext' fun _ _ ↦ rfl :
      (piRightHom R S N M).restrictScalars R = piRightHom R R N M)
  rw [hS]
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R N
  -- Five lemma on the presentation `R ^ m → R ^ n → N → 0`, tensored with the product (top row)
  -- and tensored with each factor before taking the product (bottom row).
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (g.rTensor (∀ i, M i)) (f.rTensor (∀ i, M i))
    (LinearMap.piMap fun i ↦ g.rTensor (M i)) (LinearMap.piMap fun i ↦ f.rTensor (M i))
    (piRightHom R R (Fin m → R) M) (piRightHom R R (Fin n → R) M) (piRightHom R R N M)
    (piRightHom_comp_rTensor g).symm (piRightHom_comp_rTensor f).symm
    (rTensor_exact _ hfg hf) (Function.Exact.piMap fun i ↦ rTensor_exact (M i) hfg hf)
    (piRightHom_bijective_of_finite_free R M (Fin m)).surjective
    (piRightHom_bijective_of_finite_free R M (Fin n))
    (LinearMap.rTensor_surjective _ hf)
    (Function.Surjective.piMap fun i ↦ LinearMap.rTensor_surjective (M i) hf)

end CommRing

end TensorProduct
