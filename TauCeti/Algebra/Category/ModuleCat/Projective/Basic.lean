/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Categorical and module projectivity

A module that is projective as an object of `ModuleCat` and receives a surjection from a
projective module is a projective module. No smallness assumption on the ring is needed: the
splitting of the surjection is produced by the lifting property of the object itself.

## Main results

* `LinearMap.moduleProjective_of_projective_of_surjective`: categorical projectivity of a module
  that is the image of a projective module gives `Module.Projective`.
* `ModuleCat.exists_retract_pi_of_finite_projective`: a finitely generated projective module is a
  retract of a finite free module.
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

/-- **A finitely generated projective module is a retract of a finite free module.** -/
theorem ModuleCat.exists_retract_pi_of_finite_projective (M : ModuleCat.{u} R) [Module.Finite R M]
    [Module.Projective R M] : ∃ k : ℕ, Nonempty (Retract M (ModuleCat.of R (Fin k → R))) := by
  obtain ⟨k, f, s, -, -, hs⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨k, ⟨⟨ModuleCat.ofHom s, ModuleCat.ofHom f, by ext x; exact congr($hs x)⟩⟩⟩
