/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change of a tensor product, and injectivity of base-change maps

If `f : M →ₗ[R] N` and `g : M' →ₗ[R] N'` exhibit the `S`-modules `N` and `N'` as base changes of
`M` and `M'` along `R → S`, then `m ⊗ m' ↦ f m ⊗ g m'` exhibits `N ⊗[S] N'` as the base change of
`M ⊗[R] M'`. On the concrete models this is Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange`,
`S ⊗[R] (M ⊗[R] M') ≃ (S ⊗[R] M) ⊗[S] (S ⊗[R] M')`; the statement here is its form for the
abstract `IsBaseChange` interface, alongside Mathlib's `IsBaseChange.prodMap` for products.
Mathlib's `isBaseChange_tensorProduct_map` is the analogous statement when only one factor is
base changed and the tensor product stays over the base ring.

If `f : M →ₗ[R] N` exhibits `N` as the base change of `M` along `R → S`, then the `S`-linear map
`S ⊗[R] M →ₗ[S] N` it induces, Mathlib's `LinearMap.liftBaseChange`, is bijective: it is the
equivalence `IsBaseChange.equiv`.
The original map `f` is also injective whenever the scalar-unit map `m ↦ 1 ⊗ m` is injective.

Base change of linear maps is compatible with the induced maps `S ⊗[R] M →ₗ[S] N`: a commutative
square of `R`-linear maps gives a commutative square of the induced `S`-linear maps. The map
induced on a finite product is injective as soon as each factor induces an injective map.

For any localization, extension also preserves injectivity of a linear map into a module over
the localized semiring, without requiring its image to span the target.

## Main results

* `IsBaseChange.tensorProduct`: a tensor product of base changes is a base change of the tensor
  product.
* `IsBaseChange.liftBaseChange_bijective`, `IsBaseChange.liftBaseChange_injective`: the map
  `S ⊗[R] M →ₗ[S] N` induced by a base change is bijective, in particular injective.
* `IsBaseChange.injective_of_tensorProduct_mk_injective`: a base-change map is injective when
  the scalar-unit map `M → S ⊗[R] M` is injective.
* `LinearMap.liftBaseChange_comp_baseChange`: naturality of the induced map `S ⊗[R] M → N`.
* `LinearMap.liftBaseChange_pi_injective`: injectivity of the induced map on finite products.
* `LinearMap.liftBaseChange_injective`: extension to a localization preserves injectivity of a
  map into a module over the localized semiring, without a full-span hypothesis.
-/

public section

open scoped TensorProduct

variable {R S M M' N N' : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommMonoid N'] [Module R N'] [Module S N'] [IsScalarTower R S N']

/-- **Base change commutes with tensor products.** If `f` and `g` exhibit `N` and `N'` as base
changes of `M` and `M'` along `R → S`, then `m ⊗ m' ↦ f m ⊗ g m'` exhibits `N ⊗[S] N'` as the
base change of `M ⊗[R] M'`. -/
theorem IsBaseChange.tensorProduct {f : M →ₗ[R] N} {g : M' →ₗ[R] N'}
    (hf : IsBaseChange S f) (hg : IsBaseChange S g) :
    IsBaseChange S (TensorProduct.mapOfCompatibleSMul S R R N N' ∘ₗ TensorProduct.map f g) := by
  refine IsBaseChange.of_equiv
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R S M M').trans
      (TensorProduct.congr hf.equiv hg.equiv)) fun x ↦ ?_
  induction x with
  | tmul m m' => simp [IsBaseChange.equiv_tmul]
  | add x y hx hy => simp_all [TensorProduct.tmul_add]

/-- If `f` exhibits `N` as the base change of `M` along `R → S`, then the induced `S`-linear map
`f.liftBaseChange S : S ⊗[R] M →ₗ[S] N` is bijective, since it is the equivalence `hf.equiv`. -/
theorem IsBaseChange.liftBaseChange_bijective {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    Function.Bijective (f.liftBaseChange S) := by
  have : f.liftBaseChange S = hf.equiv.toLinearMap := by
    ext
    simp [IsBaseChange.equiv_tmul]
  rw [this]
  exact hf.equiv.bijective

/-- If `f` exhibits `N` as the base change of `M` along `R → S`, then the induced `S`-linear map
`f.liftBaseChange S : S ⊗[R] M →ₗ[S] N` is injective, since it is the equivalence `hf.equiv`. -/
theorem IsBaseChange.liftBaseChange_injective {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    Function.Injective (f.liftBaseChange S) :=
  hf.liftBaseChange_bijective.1

/-- A base-change map is injective whenever the scalar-unit map `m ↦ 1 ⊗ m` is injective,
since the original map factors through this map and the base-change equivalence. -/
theorem IsBaseChange.injective_of_tensorProduct_mk_injective {f : M →ₗ[R] N}
    (hf : IsBaseChange S f) (hinj : Function.Injective (TensorProduct.mk R S M 1)) :
    Function.Injective f := by
  intro x y hxy
  apply hinj
  apply hf.equiv.injective
  simpa only [TensorProduct.mk_apply, hf.equiv_tmul, one_smul] using hxy

section

variable (S) {M₁ M₂ N₁ N₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁]
  [AddCommMonoid N₂] [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂] [Module S N₁]
  [Module S N₂] [IsScalarTower R S N₁] [IsScalarTower R S N₂]

/-- The base change of `f` followed by the map induced by `h₂` is the map induced by `h₁` followed
by `f'`, whenever `h₂ ∘ f = f' ∘ h₁`. -/
theorem LinearMap.liftBaseChange_comp_baseChange {h₁ : M₁ →ₗ[R] N₁} {h₂ : M₂ →ₗ[R] N₂}
    {f : M₁ →ₗ[R] M₂} {f' : N₁ →ₗ[S] N₂}
    (comm : h₂.comp f = (f'.restrictScalars R).comp h₁) :
    (h₂.liftBaseChange S).comp (f.baseChange S) = f'.comp (h₁.liftBaseChange S) := by
  ext m
  simpa using congr($comm m)

/-- The map `S ⊗[R] (∀ i, M i) → ∀ i, N i` induced by a finite product of maps `f i : M i → N i` is
injective if each `S ⊗[R] M i → N i` is. -/
theorem LinearMap.liftBaseChange_pi_injective {ι : Type*} [Finite ι] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (M i)]
    [∀ i, Module R (N i)] [∀ i, Module S (N i)] [∀ i, IsScalarTower R S (N i)]
    (f : ∀ i, M i →ₗ[R] N i) (hf : ∀ i, Function.Injective ((f i).liftBaseChange S)) :
    Function.Injective ((LinearMap.pi fun i ↦ f i ∘ₗ LinearMap.proj i).liftBaseChange S) := by
  classical
  cases nonempty_fintype ι
  have h : (LinearMap.pi fun i ↦ f i ∘ₗ LinearMap.proj i).liftBaseChange S =
      (LinearMap.pi fun i ↦ (f i).liftBaseChange S ∘ₗ LinearMap.proj i) ∘ₗ
        (TensorProduct.piRight R S S M).toLinearMap := by
    ext x i
    simp
  rw [h, LinearMap.coe_comp]
  exact Function.Injective.comp (fun _ _ hxy ↦ funext fun i ↦ hf i (congrFun hxy i))
    (TensorProduct.piRight R S S M).injective

end

section

variable {R K M V : Type*} [CommSemiring R] [CommSemiring K] [Algebra R K]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- For a localization `K = S⁻¹R`, extension of an injective `R`-linear map into a `K`-module
remains injective. Neither freeness, finite generation nor a full-span hypothesis is needed. -/
theorem LinearMap.liftBaseChange_injective (f : M →ₗ[R] V) (S : Submonoid R)
    [IsLocalization S K] (hf : Function.Injective f) : Function.Injective (f.liftBaseChange K) := by
  refine IsLocalizedModule.injective_of_map_eq S (TensorProduct.mk R K M 1)
    (g := (f.liftBaseChange K).restrictScalars R) ?_
  intro x y h
  exact congrArg (fun m ↦ 1 ⊗ₜ[R] m) (hf (by simpa using h))

end
