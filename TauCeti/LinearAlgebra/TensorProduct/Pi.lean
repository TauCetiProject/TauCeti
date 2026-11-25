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
import Mathlib.RingTheory.TensorProduct.Pi
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

For an `R`-algebra `N` and a finite index type, the identification
`TensorProduct.piScalarRight : N ⊗[R] (ι → R) ≃ (ι → N)` sends `1 ⊗ x` to the coordinatewise image
`algebraMap R N ∘ x` (`TensorProduct.piScalarRight_one_tmul`). Transporting the base change of a
linear equivalence `(ι → R) ≃ (κ → R)` along it gives its scalar extension `(ι → A) ≃ (κ → A)`
(`LinearEquiv.extendScalarsPi`), which acts on vectors with coordinates in `R` as the original
equivalence and is compatible with identities, composition and inverses.

## Main definitions

* `LinearEquiv.extendScalarsPi`: the scalar extension of a linear equivalence between coordinate
  spaces.
* `Module.Basis.tensorPiEquiv`: for a basis `e` of an `A`-module `W`, the identification
  `A ⊗[R] (ι → R) ≃ W` of the base change of the coordinate space with `W`.

## Main results

* `TensorProduct.piRightHom_comp_rTensor`: naturality of `TensorProduct.piRightHom` in the
  left factor.
* `TensorProduct.piRightHom_bijective_of_finitePresentation`: tensoring with a finitely presented
  module commutes with arbitrary products.
* `TensorProduct.piScalarRight_one_tmul`: `1 ⊗ x` corresponds to `algebraMap R N ∘ x`.
* `LinearEquiv.extendScalarsPi_apply_algebraMap_comp`: the scalar extension of `e` carries
  `algebraMap R A ∘ v` to `algebraMap R A ∘ e v`.
* `LinearEquiv.extendScalarsPi_refl`, `LinearEquiv.extendScalarsPi_trans`,
  `LinearEquiv.extendScalarsPi_symm`: functoriality of the scalar extension.
* `TensorProduct.piScalarRight_tmul_eq_smul`: for a commutative `R`-algebra `A`, the
  identification `A ⊗[R] (ι → R) ≃ (ι → A)` sends `a ⊗ v` to `a • (algebraMap R A ∘ v)`.
* `TensorProduct.piScalarRight_symm_algebraMap_comp`: conversely, `algebraMap R N ∘ v`
  corresponds to the pure tensor `1 ⊗ v`.
* `TensorProduct.piScalarRight_rTensor`: `piScalarRight` is natural in the module.

## References

* S. U. Chase, *Direct products of modules*, Trans. Amer. Math. Soc. 97 (1960), §2.
-/

public section

open scoped TensorProduct

namespace TensorProduct

section ScalarExtension

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] (ι : Type*) [Fintype ι]
  [DecidableEq ι] {N : Type*} [Semiring N] [Algebra R N] [Module S N] [IsScalarTower R S N]

/-- The identification `N ⊗[R] (ι → R) ≃ (ι → N)` sends `1 ⊗ x` to `x` read in `ι → N`. This is
the forward direction of Mathlib's `TensorProduct.piScalarRight_symm_algebraMap`. -/
theorem piScalarRight_one_tmul (x : ι → R) :
    piScalarRight R S N ι (1 ⊗ₜ x) = algebraMap R N ∘ x := by
  ext i
  simp [piScalarRight_apply, piScalarRightHom_tmul, Algebra.algebraMap_eq_smul_one]

end ScalarExtension

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
    piScalarRight R A A ι (a ⊗ₜ v) = a • (algebraMap R A ∘ v) := by
  ext i
  simp [_root_.Algebra.smul_def, mul_comm]

/-- A vector with coordinates mapped from `R` corresponds to the pure tensor `1 ⊗ v`. This is
Mathlib's `TensorProduct.piScalarRight_symm_algebraMap` with the vector written as a composite,
the form in which it can be rewritten with. -/
theorem piScalarRight_symm_algebraMap_comp {S N : Type*} [CommSemiring S] [Algebra R S]
    [Semiring N] [Algebra R N] [Module S N] [IsScalarTower R S N] (v : ι → R) :
    (piScalarRight R S N ι).symm (algebraMap R N ∘ v) = 1 ⊗ₜ v :=
  piScalarRight_symm_algebraMap R S ι v

/-- `TensorProduct.piScalarRight` is natural in the module: a linear map `φ : N → N'` acting on
the left factor of `N ⊗ (ι → R)` acts coordinatewise on `ι → N`. The scalar ring `S` of the
right-hand side does not occur on the left, so it is explicit. -/
theorem piScalarRight_rTensor (S : Type*) {S' N N' : Type*} [CommSemiring S] [Algebra R S]
    [CommSemiring S'] [Algebra R S'] [AddCommMonoid N] [Module R N] [Module S N]
    [IsScalarTower R S N] [AddCommMonoid N'] [Module R N'] [Module S' N'] [IsScalarTower R S' N']
    (φ : N →ₗ[R] N') (x : N ⊗[R] (ι → R)) :
    piScalarRight R S' N' ι (LinearMap.rTensor (ι → R) φ x) = φ ∘ piScalarRight R S N ι x := by
  induction x using TensorProduct.inductionOn with
  | tmul a f => ext i; simp
  | add x y hx hy => ext i; simp only [map_add, hx, hy, Pi.add_apply, Function.comp_apply]

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

namespace LinearEquiv

open TensorProduct

variable {R : Type*} (A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
variable {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-- The scalar extension of a linear equivalence `e : (ι → R) ≃ (κ → R)` to an `R`-algebra `A`:
the base change `A ⊗[R] (ι → R) ≃ A ⊗[R] (κ → R)` of `e`, transported to coordinates along
`TensorProduct.piScalarRight`. It carries `algebraMap R A ∘ v` to `algebraMap R A ∘ e v`
(`LinearEquiv.extendScalarsPi_apply_algebraMap_comp`). -/
noncomputable def extendScalarsPi (e : (ι → R) ≃ₗ[R] (κ → R)) : (ι → A) ≃ₗ[A] (κ → A) :=
  (piScalarRight R A A ι).symm ≪≫ₗ e.baseChange R A _ _ ≪≫ₗ piScalarRight R A A κ

/-- The scalar extension of `e` acts on vectors with coordinates in `R` as `e`. -/
@[simp]
theorem extendScalarsPi_apply_algebraMap_comp (e : (ι → R) ≃ₗ[R] (κ → R)) (v : ι → R) :
    e.extendScalarsPi A (algebraMap R A ∘ v) = algebraMap R A ∘ e v := by
  rw [extendScalarsPi, trans_apply, trans_apply, ← piScalarRight_one_tmul R A ι,
    symm_apply_apply, baseChange_tmul, piScalarRight_one_tmul]

/-- The scalar extension of the identity is the identity. -/
@[simp]
theorem extendScalarsPi_refl : (refl R (ι → R)).extendScalarsPi A = refl A (ι → A) := by
  ext x : 1
  simp only [extendScalarsPi, trans_apply, refl_apply]
  rw [← one_eq_refl, baseChange_one, one_eq_refl, refl_apply, apply_symm_apply]

/-- The scalar extension of a composite is the composite of the scalar extensions. -/
theorem extendScalarsPi_trans (e : (ι → R) ≃ₗ[R] (κ → R)) (f : (κ → R) ≃ₗ[R] (μ → R)) :
    (e.trans f).extendScalarsPi A = (e.extendScalarsPi A).trans (f.extendScalarsPi A) := by
  ext x : 1
  simp only [extendScalarsPi, baseChange_trans, trans_apply, symm_apply_apply]

/-- The scalar extension of the inverse is the inverse of the scalar extension. -/
theorem extendScalarsPi_symm (e : (ι → R) ≃ₗ[R] (κ → R)) :
    e.symm.extendScalarsPi A = (e.extendScalarsPi A).symm := by
  ext x : 1
  simp only [extendScalarsPi, baseChange_symm, trans_apply, symm_trans_apply, symm_symm]

end LinearEquiv

namespace Module.Basis

variable (R : Type*) {A W ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid W] [Module A W] [Fintype ι] [DecidableEq ι]

/-- For a basis `e` of an `A`-module `W` and an `R`-algebra `A`, the identification
`A ⊗[R] (ι → R) ≃ W` of the base change of `ι → R` with `W`, sending `a ⊗ x` to
`a • ∑ i, algebraMap R A (x i) • e i`. -/
noncomputable def tensorPiEquiv (e : Basis ι A W) : A ⊗[R] (ι → R) ≃ₗ[A] W :=
  (TensorProduct.piScalarRight R A A ι).trans e.equivFun.symm

/-- The pure tensor `a ⊗ x` corresponds to `a • ∑ i, algebraMap R A (x i) • e i`. -/
@[simp]
theorem tensorPiEquiv_tmul (e : Basis ι A W) (a : A) (x : ι → R) :
    e.tensorPiEquiv R (a ⊗ₜ x) = a • ∑ i, algebraMap R A (x i) • e i := by
  simp [tensorPiEquiv, Finset.smul_sum, smul_smul, Algebra.smul_def, mul_comm]

/-- The inverse of `e.tensorPiEquiv R` takes a vector to its coordinates in `e`, read in
`A ⊗[R] (ι → R)`. -/
@[simp]
theorem tensorPiEquiv_symm_apply (e : Basis ι A W) (v : W) :
    (e.tensorPiEquiv R).symm v = (TensorProduct.piScalarRight R A A ι).symm (e.repr v) := by
  simp [tensorPiEquiv]

end Module.Basis
