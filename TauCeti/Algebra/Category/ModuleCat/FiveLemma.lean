/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The five lemma for ladders of modules

Mathlib's five lemma for additive groups
(`AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective`) and its special
case for rows starting with injective maps
(`AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact`) take exactness as
`Function.Exact` and commutativity as equalities of composites of additive maps. Long exact
sequences in homological algebra instead provide exactness of the short complexes
`ShortComplex.mk f g w` of morphisms in `ModuleCat`, and commutative squares as equalities of
composites of morphisms. This file restates the two lemmas in that form, for modules over any ring.

## Main results

* `ModuleCat.bijective_of_surjective_of_bijective_of_bijective_of_injective`: the five lemma.
* `ModuleCat.bijective_of_bijective_of_injective_of_left_exact`: the five lemma for a ladder of
  three-term exact rows starting with monomorphisms.
-/

public section

open CategoryTheory Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- **The five lemma** for a ladder of exact sequences of modules, with exactness stated for short
complexes. -/
theorem bijective_of_surjective_of_bijective_of_bijective_of_injective
    {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : ModuleCat.{v} R}
    {f₁ : M₁ ⟶ M₂} {f₂ : M₂ ⟶ M₃} {f₃ : M₃ ⟶ M₄} {f₄ : M₄ ⟶ M₅}
    {g₁ : N₁ ⟶ N₂} {g₂ : N₂ ⟶ N₃} {g₃ : N₃ ⟶ N₄} {g₄ : N₄ ⟶ N₅}
    {i₁ : M₁ ⟶ N₁} {i₂ : M₂ ⟶ N₂} {i₃ : M₃ ⟶ N₃} {i₄ : M₄ ⟶ N₄} {i₅ : M₅ ⟶ N₅}
    {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0} {w₃ : f₃ ≫ f₄ = 0}
    {v₁ : g₁ ≫ g₂ = 0} {v₂ : g₂ ≫ g₃ = 0} {v₃ : g₃ ≫ g₄ = 0}
    (hf₁ : (ShortComplex.mk f₁ f₂ w₁).Exact) (hf₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (hf₃ : (ShortComplex.mk f₃ f₄ w₃).Exact) (hg₁ : (ShortComplex.mk g₁ g₂ v₁).Exact)
    (hg₂ : (ShortComplex.mk g₂ g₃ v₂).Exact) (hg₃ : (ShortComplex.mk g₃ g₄ v₃).Exact)
    (sq₁ : f₁ ≫ i₂ = i₁ ≫ g₁) (sq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) (sq₃ : f₃ ≫ i₄ = i₃ ≫ g₃)
    (sq₄ : f₄ ≫ i₅ = i₄ ≫ g₄) (hi₁ : Function.Surjective i₁) (hi₂ : Function.Bijective i₂)
    (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) : Function.Bijective i₃ :=
  AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁.hom.toAddMonoidHom f₂.hom.toAddMonoidHom f₃.hom.toAddMonoidHom f₄.hom.toAddMonoidHom
    g₁.hom.toAddMonoidHom g₂.hom.toAddMonoidHom g₃.hom.toAddMonoidHom g₄.hom.toAddMonoidHom
    i₁.hom.toAddMonoidHom i₂.hom.toAddMonoidHom i₃.hom.toAddMonoidHom i₄.hom.toAddMonoidHom
    i₅.hom.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom sq₁ x).symm)
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom sq₂ x).symm)
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom sq₃ x).symm)
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom sq₄ x).symm)
    (LinearMap.exact_iff.2 hf₁.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hf₂.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hf₃.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₁.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₂.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₃.moduleCat_range_eq_ker.symm) hi₁ hi₂ hi₄ hi₅

/-- **The five lemma** for a ladder of three-term exact sequences of modules starting with
monomorphisms, with exactness stated for short complexes. -/
theorem bijective_of_bijective_of_injective_of_left_exact {M₁ M₂ M₃ N₁ N₂ N₃ : ModuleCat.{v} R}
    {f₁ : M₁ ⟶ M₂} {f₂ : M₂ ⟶ M₃} {g₁ : N₁ ⟶ N₂} {g₂ : N₂ ⟶ N₃}
    {i₁ : M₁ ⟶ N₁} {i₂ : M₂ ⟶ N₂} {i₃ : M₃ ⟶ N₃} {w : f₁ ≫ f₂ = 0} {v : g₁ ≫ g₂ = 0}
    (hf : (ShortComplex.mk f₁ f₂ w).Exact) (hg : (ShortComplex.mk g₁ g₂ v).Exact)
    [Mono f₁] [Mono g₁] (sq₁ : f₁ ≫ i₂ = i₁ ≫ g₁) (sq₂ : f₂ ≫ i₃ = i₂ ≫ g₂)
    (hi₂ : Function.Bijective i₂) (hi₃ : Function.Injective i₃) : Function.Bijective i₁ :=
  AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
    f₁.hom.toAddMonoidHom f₂.hom.toAddMonoidHom g₁.hom.toAddMonoidHom g₂.hom.toAddMonoidHom
    i₁.hom.toAddMonoidHom i₂.hom.toAddMonoidHom i₃.hom.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom sq₁ x).symm)
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom sq₂ x).symm)
    (LinearMap.exact_iff.2 hf.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg.moduleCat_range_eq_ker.symm) hi₂ hi₃
    ((ModuleCat.mono_iff_injective _).1 inferInstance)
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

end ModuleCat
