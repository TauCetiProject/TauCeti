/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.Basic
public import TauCeti.Algebra.Module.Generator
public import TauCeti.CategoryTheory.Preadditive.Progenerator

/-!
# Progenerators in full subcategories of `ModuleCat`

Let `S : ObjectProperty (ModuleCat.{v} R)` be an object property of `R`-modules. Building on the
characterization of projective objects in `S.FullSubcategory`
(`TauCeti.Algebra.Category.ModuleCat.Projective.Basic`), this file relates categorical
progenerators (`TauCeti.IsProgenerator`) in `S.FullSubcategory` to module-theoretic projectivity
(`Module.Projective`) and generators (`TauCeti.Module.IsGenerator`).

* When `S` is closed under finite products and contains an object linearly equivalent to `R`, every
  progenerator of `S.FullSubcategory` is a module-theoretic generator whenever `S.ι` preserves
  epimorphisms (`CategoryTheory.ObjectProperty.isGenerator_of_isProgenerator`).
* When `S ≤ ModuleCat.isFG R` and `S` is closed under finite products, every projective object
  `P : S.FullSubcategory` whose underlying `R`-module is a generator is a progenerator of
  `S.FullSubcategory` (`CategoryTheory.ObjectProperty.isProgenerator_of_projective_of_isGenerator`).

Combining both directions yields the full characterization
`CategoryTheory.ObjectProperty.isProgenerator_iff_moduleProjective_and_isGenerator`, which
specializes uniformly to both `FGModuleCat R` (`TauCeti.Algebra.Category.FGModuleCat.Progenerator`)
and `(TauCeti.finitePresentationModules R).FullSubcategory`
(`TauCeti.Algebra.Category.ModuleCat.FinitePresentation.Progenerator`).

## Main results

* `CategoryTheory.ObjectProperty.isProgenerator_of_projective_of_isGenerator`,
  `CategoryTheory.ObjectProperty.isGenerator_of_isProgenerator`, and
  `CategoryTheory.ObjectProperty.isProgenerator_iff_moduleProjective_and_isGenerator`:
  correspondence between `TauCeti.IsProgenerator P` in `S.FullSubcategory` and
  `Module.Projective R P.obj ∧ TauCeti.Module.IsGenerator R P.obj`.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189, Springer (1999),
  §18.
-/

public section

namespace CategoryTheory.ObjectProperty

open CategoryTheory.Limits TauCeti

universe u v

variable {R : Type u} [Ring R] (S : ObjectProperty (ModuleCat.{v} R))

/-- In a full subcategory `S.FullSubcategory` of finitely generated `R`-modules closed under finite
products, any projective object whose underlying `R`-module is a generator is a progenerator. -/
theorem isProgenerator_of_projective_of_isGenerator [S.IsClosedUnderFiniteProducts]
    (hS : S ≤ ModuleCat.isFG.{v} R) (P : S.FullSubcategory)
    [Projective P] [TauCeti.Module.IsGenerator R P.obj] :
    IsProgenerator P where
  exists_epi_biproduct X := by
    have : Module.Finite R X.obj := (ModuleCat.isFG_iff X.obj).mp (hS X.obj X.property)
    obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' R X.obj
    obtain ⟨k, p, hp⟩ :=
      (TauCeti.Module.isGenerator_iff_exists_surjective (R := R) (M := P.obj)).mp inferInstance
    let eFin : (Fin (m * k) → P.obj) ≃ₗ[R] (Fin m → Fin k → P.obj) :=
      (LinearEquiv.funCongrLeft R P.obj finProdFinEquiv).trans
        (LinearEquiv.curry R P.obj (Fin m) (Fin k))
    let pMap : (Fin m → Fin k → P.obj) →ₗ[R] (Fin m → R) :=
      LinearMap.pi fun i ↦ p ∘ₗ LinearMap.proj i
    have hpMap : Function.Surjective pMap := fun f ↦ by
      choose g hg using fun i ↦ hp (f i)
      exact ⟨g, funext hg⟩
    let φ : (Fin (m * k) → P.obj) →ₗ[R] X.obj := q ∘ₗ pMap ∘ₗ eFin.toLinearMap
    have hφ : Function.Surjective φ := hq.comp (hpMap.comp eFin.surjective)
    exact ⟨m * k, _, S.epi_homMk_biproductObjIsoPi_comp hφ⟩

/-- A progenerator of a full subcategory `S.FullSubcategory` of `ModuleCat R` is a generator as an
`R`-module, provided `S` is closed under finite products, `S.ι` preserves epimorphisms, and `S`
contains an object linearly equivalent to `R`. -/
theorem isGenerator_of_isProgenerator [S.IsClosedUnderFiniteProducts] [S.ι.PreservesEpimorphisms]
    {R₀ : S.FullSubcategory} (eR : R₀.obj ≃ₗ[R] R)
    {P : S.FullSubcategory} (hP : IsProgenerator P) :
    TauCeti.Module.IsGenerator R P.obj := by
  obtain ⟨n, π, hπ⟩ := hP.exists_epi_biproduct R₀
  exact (TauCeti.Module.isGenerator_iff_exists_surjective (R := R) (M := P.obj)).mpr
    ⟨n, eR.toLinearMap ∘ₗ ((S.biproductObjIsoPi _).inv ≫ π.hom).hom,
      eR.surjective.comp (S.surjective_biproductObjIsoPi_inv_comp π)⟩

/-- Characterization of progenerators in a full subcategory `S.FullSubcategory` of finitely
generated `R`-modules closed under finite products whose inclusion preserves epimorphisms and which
contains an object linearly equivalent to `R`: an object `P` is a categorical progenerator if and
only if its underlying `R`-module is projective and a generator. -/
theorem isProgenerator_iff_moduleProjective_and_isGenerator [S.IsClosedUnderFiniteProducts]
    [S.ι.PreservesEpimorphisms] (hS : S ≤ ModuleCat.isFG.{v} R)
    {R₀ : S.FullSubcategory} (eR : R₀.obj ≃ₗ[R] R) (P : S.FullSubcategory) :
    IsProgenerator P ↔ Module.Projective R P.obj ∧ TauCeti.Module.IsGenerator R P.obj := by
  have : Module.Finite R P.obj := (ModuleCat.isFG_iff P.obj).mp (hS P.obj P.property)
  refine ⟨fun hP ↦ ?_, fun ⟨_, _⟩ ↦ ?_⟩
  · have := hP.projective
    exact ⟨S.moduleProjective_of_projective eR P, S.isGenerator_of_isProgenerator eR hP⟩
  · have := S.projective_of_moduleProjective P
    exact S.isProgenerator_of_projective_of_isGenerator hS P

end CategoryTheory.ObjectProperty
