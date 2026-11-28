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
# Projective objects in full subcategories of `ModuleCat`

For a full subcategory `S.FullSubcategory` of `ModuleCat.{v} R`:

* Whenever `S.ι` preserves epimorphisms, any `P : S.FullSubcategory` whose underlying module is
  projective is a projective object of `S.FullSubcategory`
  (`CategoryTheory.ObjectProperty.projective_of_moduleProjective`).
* Conversely, when `S` is closed under finite products and contains an object linearly equivalent
  to `R`, every finitely generated projective object of `S.FullSubcategory` is projective as an
  `R`-module (`CategoryTheory.ObjectProperty.moduleProjective_of_projective`), yielding the
  equivalence `CategoryTheory.ObjectProperty.projective_iff_moduleProjective`.

## Main results

* `CategoryTheory.ObjectProperty.projective_of_moduleProjective`,
  `CategoryTheory.ObjectProperty.moduleProjective_of_projective`, and
  `CategoryTheory.ObjectProperty.projective_iff_moduleProjective`: correspondence between
  categorical projectivity in `S.FullSubcategory` and `Module.Projective R P.obj`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

universe u v

variable {R : Type u} [Ring R] (S : ObjectProperty (ModuleCat.{v} R))

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
  let π : (⨁ fun _ : Fin n ↦ R₀) ⟶ P :=
    ObjectProperty.homMk
      ((S.biproductObjIsoPi fun _ : Fin n ↦ R₀).hom ≫ ModuleCat.ofHom (q ∘ₗ eFin.toLinearMap))
  have : Epi π := S.epi_homMk_biproductObjIsoPi_comp (hq.comp eFin.surjective)
  let r : Retract P (⨁ fun _ : Fin n ↦ R₀) :=
    ⟨Projective.factorThru (𝟙 P) π, π, Projective.factorThru_comp (𝟙 P) π⟩
  have : Small.{v} R := ⟨⟨R₀.obj, ⟨eR.toEquiv.symm⟩⟩⟩
  have : Module.Projective R (Fin n → R₀.obj) := Module.Projective.of_equiv' eFin.symm
  have : Projective (ModuleCat.of R (Fin n → R₀.obj)) := inferInstance
  have : Projective (S.ι.obj (⨁ fun _ : Fin n ↦ R₀)) :=
    Projective.of_iso (S.biproductObjIsoPi _).symm inferInstance
  have : Projective P.obj := (r.map S.ι).projective
  exact inferInstance

/-- Characterization of finitely generated projective objects in `S.FullSubcategory` when `S` is
closed under finite products, `S.ι` preserves epimorphisms, and `S` contains an object linearly
equivalent to `R`. -/
theorem projective_iff_moduleProjective [S.IsClosedUnderFiniteProducts]
    [S.ι.PreservesEpimorphisms] {R₀ : S.FullSubcategory} (eR : R₀.obj ≃ₗ[R] R)
    (P : S.FullSubcategory) [Module.Finite R P.obj] :
    Projective P ↔ Module.Projective R P.obj :=
  ⟨fun _ ↦ S.moduleProjective_of_projective eR P, fun _ ↦ S.projective_of_moduleProjective P⟩

end CategoryTheory.ObjectProperty
