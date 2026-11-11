/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The five and four lemmas for ladders of modules

Mathlib's five and four lemmas for modules
(`LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective`,
`LinearMap.surjective_of_surjective_of_surjective_of_injective`) take exactness as
`Function.Exact` of linear maps and commutativity as equalities of composites of linear maps. Long
exact sequences in homological algebra instead provide exactness of the short complexes
`ShortComplex.mk f g w` of morphisms in `ModuleCat`, and commutative squares as equalities of
composites of morphisms. This file restates the two lemmas in that form.

## Main results

* `ModuleCat.bijective_of_exact_of_comm`: the five lemma.
* `ModuleCat.surjective_of_exact_of_comm`: the four lemma for a lower row starting with a
  monomorphism.
-/

public section

open CategoryTheory Limits

universe u v

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- **The five lemma** for a ladder of exact sequences of modules, with exactness stated for short
complexes. -/
theorem bijective_of_exact_of_comm {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : ModuleCat.{v} R}
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
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective f₁.hom f₂.hom f₃.hom
    f₄.hom g₁.hom g₂.hom g₃.hom g₄.hom i₁.hom i₂.hom i₃.hom i₄.hom i₅.hom
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₁])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₂])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₃])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₄])
    (LinearMap.exact_iff.2 hf₁.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hf₂.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hf₃.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₁.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₂.moduleCat_range_eq_ker.symm)
    (LinearMap.exact_iff.2 hg₃.moduleCat_range_eq_ker.symm) hi₁ hi₂ hi₄ hi₅

/-- **The four lemma** for a ladder of exact sequences of modules starting with a monomorphism in
the lower row, with exactness stated for short complexes. -/
theorem surjective_of_exact_of_comm {M₂ M₃ M₄ N₂ N₃ N₄ : ModuleCat.{v} R}
    {f₂ : M₂ ⟶ M₃} {f₃ : M₃ ⟶ M₄} {g₂ : N₂ ⟶ N₃} {g₃ : N₃ ⟶ N₄}
    {i₂ : M₂ ⟶ N₂} {i₃ : M₃ ⟶ N₃} {i₄ : M₄ ⟶ N₄} {w₂ : f₂ ≫ f₃ = 0} {v₂ : g₂ ≫ g₃ = 0}
    (hf₂ : (ShortComplex.mk f₂ f₃ w₂).Exact) (hg₂ : (ShortComplex.mk g₂ g₃ v₂).Exact) [Mono g₂]
    (sq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) (sq₃ : f₃ ≫ i₄ = i₃ ≫ g₃) (hi₃ : Function.Surjective i₃)
    (hi₄ : Function.Injective i₄) : Function.Surjective i₂ :=
  LinearMap.surjective_of_surjective_of_surjective_of_injective (0 : PUnit.{v + 1} →ₗ[R] M₂)
    f₂.hom f₃.hom (0 : PUnit.{v + 1} →ₗ[R] N₂) g₂.hom g₃.hom 0 i₂.hom i₃.hom i₄.hom
    (LinearMap.ext fun _ ↦ by simp)
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₂])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, sq₃])
    (LinearMap.exact_iff.2 hf₂.moduleCat_range_eq_ker.symm)
    ((LinearMap.exact_zero_iff_injective _ _).2 ((ModuleCat.mono_iff_injective _).1 inferInstance))
    (LinearMap.exact_iff.2 hg₂.moduleCat_range_eq_ker.symm) (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩)
    hi₃ hi₄

end ModuleCat
