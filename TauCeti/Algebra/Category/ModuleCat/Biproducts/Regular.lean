/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Morphisms out of the summands of the regular module

If a module `G` isomorphic to the regular module of `A` is a biproduct of modules `P j`, then every
nonzero module receives a nonzero morphism from one of the summands `P j`
(`TauCeti.exists_hom_ne_zero_of_iso_biproduct`): the morphism `G ⟶ M` sending `1` to a nonzero
element is nonzero on some summand.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace TauCeti

variable {A : Type v} [Ring A]

/-- **Every nonzero module receives a nonzero morphism from a summand of the regular module.**
If a module `G` isomorphic to the regular module of `A` is a biproduct of modules `P j`, then every
nonzero module `M` admits a nonzero morphism `P j ⟶ M` for some `j`. -/
theorem exists_hom_ne_zero_of_iso_biproduct {G : ModuleCat.{w} A} (eG : A ≃ₗ[A] G) {J : Type*}
    {P : J → ModuleCat.{w} A} [HasBiproduct P] (e : G ≅ ⨁ P) {M : ModuleCat.{w} A}
    (hM : ¬ IsZero M) : ∃ (j : J) (f : P j ⟶ M), f ≠ 0 := by
  have : Nontrivial M :=
    not_subsingleton_iff_nontrivial.mp fun h ↦ hM (ModuleCat.isZero_iff_subsingleton.mpr h)
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  -- The morphism out of `G` sending `eG 1` to `x`.
  let t : G ⟶ M := ModuleCat.ofHom (LinearMap.toSpanSingleton A M x ∘ₗ eG.symm.toLinearMap)
  have ht : e.inv ≫ t ≠ 0 := fun h ↦ hx <| by
    have h₀ : t = 0 := by simpa using congrArg (e.hom ≫ ·) h
    simpa [t] using ConcreteCategory.congr_hom h₀ (eG 1)
  obtain ⟨j, hj⟩ : ∃ j, biproduct.ι P j ≫ e.inv ≫ t ≠ 0 := by
    by_contra! hzero
    exact ht (biproduct.hom_ext' _ _ fun j ↦ by rw [hzero j, comp_zero])
  exact ⟨j, _, hj⟩

end TauCeti
