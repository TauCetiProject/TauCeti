/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Algebra.FiveLemma
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Injectivity of base-change maps along flat ring maps

Let `S` be a flat `R`-algebra. Mathlib's `IsBaseChange.of_left_exact` says that kernels commute
with base change from `R` to `S`: in a commutative diagram with left exact rows

```text
0 → M₁ --f--> M₂ --g--> M₃
    |h₁       |h₂       |h₃
    v         v         v
0 → N₁ --f'-> N₂ --g'-> N₃
```

of `R`-modules `Mᵢ` and `S`-modules `Nᵢ`, if `h₂` and `h₃` are base changes, so is `h₁`. This file
records the weaker hypotheses that suffice, in the form used to compare sections of sheaves over
covers whose overlaps are only partially controlled:

* if `f` is injective and `h₂` is a base change, the induced map `S ⊗[R] M₁ → N₁` is injective;
* if `h₂` is a base change and the induced map `S ⊗[R] M₃ → N₃` is only injective, then `h₁` is
  still a base change.

Finally, the map induced on a finite product is injective as soon as each factor induces an
injective map.

## Main results

* `LinearMap.liftBaseChange_injective_of_isBaseChange`: injectivity of `S ⊗[R] M₁ → N₁`.
* `IsBaseChange.of_left_exact_of_injective`: the variant of `IsBaseChange.of_left_exact` with an
  injective right base-change map.
* `LinearMap.liftBaseChange_pi_injective`: injectivity on finite products.
-/

public section

open TensorProduct

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

section LeftExact

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module S N₁] [Module S N₂] [Module S N₃]
  [IsScalarTower R S N₁] [IsScalarTower R S N₂] [IsScalarTower R S N₃]
  {h₁ : M₁ →ₗ[R] N₁} {h₂ : M₂ →ₗ[R] N₂} {h₃ : M₃ →ₗ[R] N₃}
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} {f' : N₁ →ₗ[S] N₂} {g' : N₂ →ₗ[S] N₃}

/-- The base change of `f` followed by the map induced by `h₂` is the map induced by `h₁` followed
by `f'`. -/
private lemma LinearMap.liftBaseChange_comp_baseChange
    (comm : h₂.comp f = (f'.restrictScalars R).comp h₁) :
    (h₂.liftBaseChange S).comp (f.baseChange S) = f'.comp (h₁.liftBaseChange S) := by
  ext m
  simpa using congr($comm m)

/-- Let `S` be flat over `R` and let `f : M₁ → M₂` be injective. If `h₂ : M₂ → N₂` is a base change
and `h₂ ∘ f = f' ∘ h₁`, then the map `S ⊗[R] M₁ → N₁` induced by `h₁` is injective. -/
theorem LinearMap.liftBaseChange_injective_of_isBaseChange [Module.Flat R S]
    (comm : h₂.comp f = (f'.restrictScalars R).comp h₁) (isb₂ : IsBaseChange S h₂)
    (inj : Function.Injective f) : Function.Injective (h₁.liftBaseChange S) := by
  refine Function.Injective.of_comp (f := f') ?_
  rw [← LinearMap.coe_comp, ← LinearMap.liftBaseChange_comp_baseChange S comm,
    LinearMap.coe_comp, LinearMap.baseChange_eq_lTensor]
  exact isb₂.liftBaseChange_injective.comp (Module.Flat.lTensor_preserves_injective_linearMap f inj)

/-- **Kernels commute with flat base change**, with an injective comparison on the right. Let `S`
be flat over `R`, and consider a commutative diagram with left exact rows
`0 → M₁ → M₂ → M₃` of `R`-modules and `0 → N₁ → N₂ → N₃` of `S`-modules. If `h₂ : M₂ → N₂` is a
base change and the map `S ⊗[R] M₃ → N₃` induced by `h₃` is injective, then `h₁ : M₁ → N₁` is a
base change. Compare `IsBaseChange.of_left_exact`, which assumes that `h₃` is a base change. -/
theorem IsBaseChange.of_left_exact_of_injective [Module.Flat R S]
    (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂)
    (isb₂ : IsBaseChange S h₂) (inj₃ : Function.Injective (h₃.liftBaseChange S))
    (exact₁ : Function.Exact f g) (inj₁ : Function.Injective f)
    (exact₂ : Function.Exact f' g') (inj₂ : Function.Injective f') : IsBaseChange S h₁ := by
  have hb : Function.Bijective (h₁.liftBaseChange S) := by
    refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
      ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
      (f'.restrictScalars R) (g'.restrictScalars R) ((h₁.liftBaseChange S).restrictScalars R)
      ((h₂.liftBaseChange S).restrictScalars R) ((h₃.liftBaseChange S).restrictScalars R)
      ?_ ?_ ?_ exact₂ ?_ inj₃ ?_ inj₂
    · exact congrArg (LinearMap.restrictScalars R)
        (LinearMap.liftBaseChange_comp_baseChange S comm₁).symm
    · exact congrArg (LinearMap.restrictScalars R)
        (LinearMap.liftBaseChange_comp_baseChange S comm₂).symm
    · exact Module.Flat.lTensor_exact S exact₁
    · exact isb₂.liftBaseChange_bijective
    · exact Module.Flat.lTensor_preserves_injective_linearMap f inj₁
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (h₁.liftBaseChange S) hb) fun x ↦ by simp

end LeftExact

/-- The map `S ⊗[R] (∀ i, M i) → ∀ i, N i` induced by a finite product of maps `f i : M i → N i` is
injective if each `S ⊗[R] M i → N i` is. -/
theorem LinearMap.liftBaseChange_pi_injective {ι : Type*} [Finite ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module R (M i)]
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
