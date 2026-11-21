/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Categorical and module projectivity

A module that is projective as an object of `ModuleCat` and receives a surjection from a
projective module is a projective module. No smallness assumption on the ring is needed: the
splitting of the surjection is produced by the lifting property of the object itself.

For a full subcategory `S.FullSubcategory` of `ModuleCat.{v} R`:

* Whenever `S.ι` preserves epimorphisms, any `P : S.FullSubcategory` whose underlying module is
  projective is a projective object of `S.FullSubcategory`
  (`CategoryTheory.ObjectProperty.projective_of_moduleProjective`).
* Conversely, when `S` is closed under finite products and contains an object linearly equivalent
  to `R`, every finitely generated projective object of `S.FullSubcategory` is projective as an
  `R`-module (`CategoryTheory.ObjectProperty.moduleProjective_of_projective`), yielding the
  equivalence `CategoryTheory.ObjectProperty.projective_iff_moduleProjective`.

## Main results

* `LinearMap.moduleProjective_of_projective_of_surjective`: categorical projectivity of a module
  that is the image of a projective module gives `Module.Projective`.
* `CategoryTheory.ObjectProperty.projective_of_moduleProjective`,
  `CategoryTheory.ObjectProperty.moduleProjective_of_projective`, and
  `CategoryTheory.ObjectProperty.projective_iff_moduleProjective`: correspondence between
  categorical projectivity in `S.FullSubcategory` and `Module.Projective R P.obj`.
-/

public section

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A module `M` that is projective as an object of `ModuleCat` and receives a surjection from a
projective module is projective: the identity of `M` lifts through the surjection, which
splits it. -/
theorem LinearMap.moduleProjective_of_projective_of_surjective {P M : Type v}
    [AddCommGroup P] [Module R P] [Module.Projective R P] [AddCommGroup M] [Module R M]
    [Projective (ModuleCat.of R M)] {f : P →ₗ[R] M} (hf : Function.Surjective f) :
    Module.Projective R M := by
  have : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  let s := Projective.factorThru (𝟙 (ModuleCat.of R M)) (ModuleCat.ofHom f)
  have hs : s ≫ ModuleCat.ofHom f = 𝟙 (ModuleCat.of R M) := Projective.factorThru_comp _ _
  exact Module.Projective.of_split s.hom f
    (by ext x; simpa using ConcreteCategory.congr_hom hs x)

namespace CategoryTheory.ObjectProperty

open CategoryTheory.Limits

variable (S : ObjectProperty (ModuleCat.{v} R))

/-- An object of `S.FullSubcategory` whose underlying `R`-module is projective is a projective
object of `S.FullSubcategory`, whenever `S.ι` preserves epimorphisms. -/
theorem projective_of_moduleProjective [S.ι.PreservesEpimorphisms]
    (P : S.FullSubcategory) [Module.Projective R P.obj] :
    Projective P :=
  S.ι.projective_of_map_projective (inferInstance : Projective P.obj)

/-- A finitely generated projective object `P` of `S.FullSubcategory` is projective as an
`R`-module, provided `S` is closed under finite products and contains an object linearly equivalent
to `R`. -/
theorem moduleProjective_of_projective [S.IsClosedUnderFiniteProducts]
    {R₀ : S.FullSubcategory} (eR : R₀.obj ≃ₗ[R] R)
    (P : S.FullSubcategory) [Module.Finite R P.obj] [Projective P] :
    Module.Projective R P.obj := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R P.obj
  let eFin : (Fin n → R₀.obj) ≃ₗ[R] (Fin n → R) := LinearEquiv.piCongrRight fun _ ↦ eR
  let φ : (Fin n → R₀.obj) →ₗ[R] P.obj := q ∘ₗ eFin.toLinearMap
  have hφ : Function.Surjective φ := hq.comp eFin.surjective
  let π : (⨁ fun _ : Fin n ↦ R₀) ⟶ P :=
    ObjectProperty.homMk ((S.biproductObjIsoPi fun _ : Fin n ↦ R₀).hom ≫ ModuleCat.ofHom φ)
  have : Epi π := S.epi_homMk_biproductObjIsoPi_comp hφ
  let s : P ⟶ (⨁ fun _ : Fin n ↦ R₀) := Projective.factorThru (𝟙 P) π
  refine Module.Projective.of_split
    (eFin.toLinearMap ∘ₗ (S.biproductObjIsoPi fun _ : Fin n ↦ R₀).hom.hom ∘ₗ s.hom.hom)
    q (LinearMap.ext fun x ↦ ?_)
  have hs : (s ≫ π).hom.hom x = x := by
    rw [Projective.factorThru_comp, ObjectProperty.FullSubcategory.id_hom,
      ModuleCat.hom_id, LinearMap.id_apply]
  simpa [π, φ, ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply] using hs

/-- Characterization of finitely generated projective objects in `S.FullSubcategory` when `S` is
closed under finite products, `S.ι` preserves epimorphisms, and `S` contains an object linearly
equivalent to `R`. -/
theorem projective_iff_moduleProjective [S.IsClosedUnderFiniteProducts]
    [S.ι.PreservesEpimorphisms] {R₀ : S.FullSubcategory} (eR : R₀.obj ≃ₗ[R] R)
    (P : S.FullSubcategory) [Module.Finite R P.obj] :
    Projective P ↔ Module.Projective R P.obj :=
  ⟨fun _ ↦ S.moduleProjective_of_projective eR P, fun _ ↦ S.projective_of_moduleProjective P⟩

end CategoryTheory.ObjectProperty
