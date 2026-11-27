/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

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
equivalence `IsBaseChange.equiv`. Conversely, this bijectivity characterizes base changes. A
linear map between two base changes of `M` that is compatible with the base-change maps is
bijective.
The original map `f` is also injective whenever the scalar-unit map `m ↦ 1 ⊗ m` is injective.

Base change of linear maps is compatible with the induced maps `S ⊗[R] M →ₗ[S] N`: a commutative
square of `R`-linear maps gives a commutative square of the induced `S`-linear maps. The map
induced on a finite product is injective as soon as each factor induces an injective map.

For any localization, extension also preserves injectivity of a linear map into a module over
the localized semiring, without requiring its image to span the target.

The image of a base change map spans its target over the extended scalars, and for an
`R'`-algebra `A` the tensors `a ⊗ f m` generate `A ⊗[R'] M'` additively.

## Main results

* `Module.Basis.isBaseChange_of_map_basis`: a map carrying a basis to a basis over extended
  scalars is a base-change map.
* `Module.Basis.isPushout_of_algebraMap_eq`: compatible bases identify an algebra as the scalar
  extension of an under-semiring model.
* `IsBaseChange.tensorProduct`: a tensor product of base changes is a base change of the tensor
  product.
* `IsBaseChange.liftBaseChange_bijective`, `IsBaseChange.liftBaseChange_injective`: the map
  `S ⊗[R] M →ₗ[S] N` induced by a base change is bijective, in particular injective.
* `IsBaseChange.iff_liftBaseChange_bijective`: conversely, bijectivity of the induced map
  characterizes base changes.
* `IsBaseChange.bijective_of_comp_eq`: a linear map between two base changes of the same module
  that is compatible with the base-change maps is bijective.
* `IsBaseChange.injective_of_tensorProduct_mk_injective`: a base-change map is injective when
  the scalar-unit map `M → S ⊗[R] M` is injective.
* `IsBaseChange.of_surjective_algebraMap`: along a surjective `algebraMap R S`, every bijective
  `R`-linear map to an `S`-module is a base-change map.
* `LinearMap.liftBaseChange_comp_baseChange`: naturality of the induced map `S ⊗[R] M → N`.
* `LinearMap.liftBaseChange_pi_injective`: injectivity of the induced map on finite products.
* `LinearMap.liftBaseChange_injective`: extension to a localization preserves injectivity of a
  map into a module over the localized semiring, without a full-span hypothesis.
* `IsBaseChange.span_range_eq_top`: the image of a base change map spans its target over `R'`.
* `IsBaseChange.cancelBaseChange`: for a base change `f : M → M'` along `R → R'` and an
  `R'`-algebra `A`, the isomorphism `A ⊗[R'] M' ≃ A ⊗[R] M` sending `a ⊗ f m` to `a ⊗ m`.
* `IsBaseChange.cancelBaseChange_trans_cancelBaseChange`: cancelling two successive base changes
  is cancelling the composite base change.
* `IsBaseChange.tensorProduct_induction`: induction on `A ⊗[R'] M'` over the tensors `a ⊗ f m`.
* `IsBaseChange.restrictScalars_cancelBaseChange`: for a ring `A`, `cancelBaseChange` is Mathlib's
  `R'`-linear `IsBaseChange.tensorEquiv`.
-/

public section

open scoped TensorProduct

/-- A linear map carrying a basis to a basis over the extended scalars is a base-change map. -/
theorem Module.Basis.isBaseChange_of_map_basis
    {A S M N ι : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N] [Module S N]
    [IsScalarTower A S N] (c : Basis ι A M) (b : Basis ι S N) (f : M →ₗ[A] N)
    (h : ∀ i, f (c i) = b i) : IsBaseChange S f := by
  have he : (Finsupp.linearCombination A b).comp c.repr.toLinearMap = f := by
    apply c.ext
    intro i
    simp [h]
  have hbase := (IsBaseChange.of_basis A b).comp_equiv c.repr (Finsupp.linearCombination A b)
  rwa [he] at hbase

/-- Compatible bases identify an algebra as the scalar extension of an under-semiring model. -/
theorem Module.Basis.isPushout_of_algebraMap_eq
    {A S C B ι : Type*} [CommSemiring A] [CommSemiring S] [CommSemiring C]
    [CommSemiring B] [Algebra A S] [Algebra A C] [Algebra S B] [Algebra C B]
    [Algebra A B] [IsScalarTower A S B] [IsScalarTower A C B]
    (c : Basis ι A C) (b : Basis ι S B)
    (h : ∀ i, algebraMap C B (c i) = b i) : Algebra.IsPushout A S C B :=
  ⟨c.isBaseChange_of_map_basis b (IsScalarTower.toAlgHom A C B).toLinearMap h⟩

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

/-- A linear map `f` exhibits `N` as the base change of `M` along `R → S` exactly when the induced
`S`-linear map `f.liftBaseChange S : S ⊗[R] M →ₗ[S] N` is bijective. -/
theorem IsBaseChange.iff_liftBaseChange_bijective {f : M →ₗ[R] N} :
    IsBaseChange S f ↔ Function.Bijective (f.liftBaseChange S) :=
  ⟨IsBaseChange.liftBaseChange_bijective, fun h ↦
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h) fun x ↦ by simp⟩

/-- **Comparison of two base changes.** If `f : M →ₗ[R] N` and `g : M →ₗ[R] N'` both exhibit
base changes of `M` along `R → S`, then every `S`-linear map `φ : N →ₗ[S] N'` with `φ ∘ f = g` is
bijective: it is the composite `hg.equiv ∘ hf.equiv.symm` of the two base-change equivalences. -/
theorem IsBaseChange.bijective_of_comp_eq {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {g : M →ₗ[R] N'} (hg : IsBaseChange S g) (φ : N →ₗ[S] N') (h : ∀ m, φ (f m) = g m) :
    Function.Bijective φ := by
  have : φ = hg.equiv.toLinearMap ∘ₗ hf.equiv.symm.toLinearMap :=
    hf.algHom_ext _ _ fun m ↦ by simp [IsBaseChange.equiv_symm_apply, IsBaseChange.equiv_tmul, h]
  rw [this]
  exact hg.equiv.bijective.comp hf.equiv.symm.bijective

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

/-- **Base change along a surjection.** If `algebraMap R S` is surjective, every bijective
`R`-linear map `f : M → N` to an `S`-module exhibits `N` as the base change of `M` to `S`. -/
theorem IsBaseChange.of_surjective_algebraMap (hS : Function.Surjective (algebraMap R S))
    {f : M →ₗ[R] N} (hf : Function.Bijective f) : IsBaseChange S f := by
  let e := LinearEquiv.ofBijective f hf
  refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g ↦ ⟨?_, ?_, ?_⟩
  · -- `g ∘ f⁻¹` is `S`-linear: every scalar of `S` comes from `R`.
    refine
      { toFun := g ∘ e.symm
        map_add' := fun x y ↦ by simp only [Function.comp_apply, map_add]
        map_smul' := fun s x ↦ ?_ }
    obtain ⟨r, rfl⟩ := hS s
    simp only [Function.comp_apply, RingHom.id_apply, algebraMap_smul, map_smul]
  · ext m
    exact congrArg g (e.symm_apply_apply m)
  · intro g' hg'
    ext n
    obtain ⟨m, rfl⟩ := hf.surjective n
    simpa [e] using LinearMap.congr_fun hg' m

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

namespace IsBaseChange

/-- The image of a base change map `f : M →ₗ[R] M'` spans `M'` over the extended scalars `R'`. -/
theorem span_range_eq_top {R R' M M' : Type*} [CommSemiring R] [CommSemiring R'] [Algebra R R']
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] {f : M →ₗ[R] M'} (hf : IsBaseChange R' f) :
    Submodule.span R' (Set.range f) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun n ↦ ?_
  induction n using hf.inductionOn with
  | tmul a => exact Submodule.subset_span ⟨a, rfl⟩
  | smul r n hn => exact Submodule.smul_mem _ r hn
  | add n₁ n₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

section CancelBaseChange

variable {R R' M M' : Type*} [CommSemiring R] [CommSemiring R'] [Algebra R R'] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
  {f : M →ₗ[R] M'} (hf : IsBaseChange R' f)
  (A : Type*) [CommSemiring A] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A]

/-- For a base change `f : M → M'` along `R → R'` and an `R'`-algebra `A`, the `A`-linear
isomorphism `A ⊗[R'] M' ≃ A ⊗[R] M` sending `a ⊗ f m` to `a ⊗ m`
(`IsBaseChange.cancelBaseChange_tmul`). For `M' = R' ⊗[R] M` with the canonical base change map
`f m = 1 ⊗ₜ m` it is Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange`. For a
ring `A` it is Mathlib's `R'`-linear `IsBaseChange.tensorEquiv`, made `A`-linear
(`IsBaseChange.restrictScalars_cancelBaseChange`). -/
noncomputable def cancelBaseChange : A ⊗[R'] M' ≃ₗ[A] A ⊗[R] M :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) hf.equiv.symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' A A M)

@[simp]
theorem cancelBaseChange_tmul (a : A) (m : M) : hf.cancelBaseChange A (a ⊗ₜ f m) = a ⊗ₜ m := by
  simp [cancelBaseChange]

@[simp]
theorem cancelBaseChange_symm_tmul (a : A) (m : M) :
    (hf.cancelBaseChange A).symm (a ⊗ₜ m) = a ⊗ₜ f m :=
  (LinearEquiv.symm_apply_eq _).2 (hf.cancelBaseChange_tmul A a m).symm

end CancelBaseChange

section CancelBaseChangeTrans

variable {R R' R'' M M' M'' : Type*} [CommSemiring R] [CommSemiring R'] [CommSemiring R'']
  [Algebra R R'] [Algebra R' R''] [Algebra R R''] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
  [AddCommMonoid M''] [Module R'' M''] [Module R' M''] [Module R M''] [IsScalarTower R' R'' M'']
  [IsScalarTower R R'' M''] [IsScalarTower R R' M''] {f : M →ₗ[R] M'} {g : M' →ₗ[R'] M''}
  (hf : IsBaseChange R' f) (hg : IsBaseChange R'' g)
  (hgf : IsBaseChange R'' (g.restrictScalars R ∘ₗ f))
  (A : Type*) [CommSemiring A] [Algebra R A] [Algebra R' A] [Algebra R'' A]
  [IsScalarTower R R' A] [IsScalarTower R' R'' A] [IsScalarTower R R'' A]

/-- **`cancelBaseChange` is transitive.** For base changes `f : M → M'` along `R → R'` and
`g : M' → M''` along `R' → R''`, cancelling `g` and then `f` is cancelling `g ∘ f`: both send
`a ⊗ g (f m)` to `a ⊗ m`. -/
theorem cancelBaseChange_trans_cancelBaseChange :
    (hg.cancelBaseChange A).trans (hf.cancelBaseChange A) = hgf.cancelBaseChange A := by
  refine LinearEquiv.symm_bijective.injective (LinearEquiv.ext fun x ↦ ?_)
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [LinearEquiv.trans_symm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end CancelBaseChangeTrans

section Induction

variable {R R' M M' : Type*} [CommSemiring R] [CommSemiring R'] [Algebra R R'] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
  {f : M →ₗ[R] M'} (hf : IsBaseChange R' f)
  (A : Type*) [CommSemiring A] [Algebra R' A]

include hf in
/-- **Induction on `A ⊗[R'] M'` for a base change `M'` of `M`.** A property of the elements of
`A ⊗[R'] M'` which is closed under addition holds as soon as it holds on the tensors `a ⊗ f m`,
since `M'` is generated over `R'` by the image of `f`. -/
@[elab_as_elim]
theorem tensorProduct_induction {motive : A ⊗[R'] M' → Prop}
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (tmul : ∀ (a : A) (m : M), motive (a ⊗ₜ f m)) (x : A ⊗[R'] M') : motive x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact add x y hx hy
  | tmul a m' =>
    induction m' using hf.inductionOn generalizing a with
    | tmul m => exact tmul a m
    | smul s n h => rw [← TensorProduct.smul_tmul]; exact h _
    | add n₁ n₂ h₁ h₂ => rw [TensorProduct.tmul_add]; exact add _ _ (h₁ a) (h₂ a)

end Induction

section TensorEquiv

variable {R R' M M' : Type*} [CommSemiring R] [CommSemiring R'] [Algebra R R'] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
  {f : M →ₗ[R] M'} (hf : IsBaseChange R' f)
  (A : Type*) [CommRing A] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A]

/-- For a ring `A`, `IsBaseChange.cancelBaseChange` restricted to `R'`-linearity is Mathlib's
`IsBaseChange.tensorEquiv`. -/
theorem restrictScalars_cancelBaseChange :
    (hf.cancelBaseChange A).restrictScalars R' = hf.tensorEquiv A := by
  refine LinearEquiv.ext fun x ↦ ?_
  induction x using hf.tensorProduct_induction A with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a m => simp [tensorEquiv, hf.equiv_symm_apply]

end TensorEquiv

end IsBaseChange
