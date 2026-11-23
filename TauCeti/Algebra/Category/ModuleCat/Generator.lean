/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Retract
public import TauCeti.Algebra.Category.ModuleCat.Equivalence
public import TauCeti.Algebra.Module.Generator
-- Private: `ModuleCat.isSeparator` (the regular module is a separator) and `Shrink.linearEquiv`.
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Module.Shrink
import Mathlib.CategoryTheory.Generator.Preadditive

/-!
# Generators and progenerators of module categories

An `R`-module `M` is a separator of `ModuleCat R`, a module that detects morphisms, exactly when it
is a generator in the sense of `TauCeti.Module.IsGenerator`: `R` is a quotient of a finite power
of `M` (`ModuleCat.isSeparator_iff_isGenerator`). If `M` is a separator, the quotient map
`R ⟶ R ⧸ τ` by the trace ideal `τ` of `M` vanishes on every morphism out of `M`, so `τ = R`.
The same description of the separators of `FGModuleCat R`
(`FGModuleCat.isSeparator_iff_isGenerator`) is deduced from this one.

A **progenerator** of `R` is a finitely generated projective generator. Every finitely generated
projective module is a retract of a finite power of any generator
(`ModuleCat.exists_retract_pi_of_isGenerator_of_projective`); for the generator `R` this is a
retract of a finite free module (`ModuleCat.exists_retract_pi_of_projective`). In particular each of
two progenerators is a retract of a finite power of the other.

An equivalence `e : ModuleCat A ≌ ModuleCat B` carries the regular module `A` to a progenerator of
`B`: finite generation and projectivity are preserved by `e`, and the image of a separator is a
separator. This is the `ModuleCat` analogue of
`CategoryTheory.Equivalence.isGenerator_functor_obj_regular` for finitely generated modules.

## Main results

* `ModuleCat.isSeparator_iff_isGenerator`: the separators of `ModuleCat R` are the generators.
* `ModuleCat.exists_retract_pi_of_isGenerator_of_projective`: a finitely generated projective
  module is a retract of a finite power of a generator.
* `ModuleCat.exists_retract_pi_of_projective`: a finitely generated projective module is a retract
  of a finite free module `Rⁿ`.
* `CategoryTheory.Equivalence.isGenerator_functor_obj_self`: an equivalence of module categories
  carries the regular module to a generator; with `finite_functor_obj_self` and
  `projective_functor_obj_self` (`Algebra/Category/ModuleCat/Equivalence.lean`), to a
  progenerator.

## References

* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., GTM 13, Springer (1992),
  §§8, 17 and 22.
* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189, §18.
-/

public section

universe v u u'

open CategoryTheory TauCeti

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- **A generator is a separator** of `ModuleCat R`: the images of the morphisms out of a generator
span every module. -/
theorem isSeparator_of_isGenerator (M : ModuleCat.{v} R) [Module.IsGenerator R M] :
    IsSeparator M := by
  refine (Preadditive.isSeparator_iff _).2 fun X Y f hf ↦ ?_
  have h : ⨆ g : M →ₗ[R] X, LinearMap.range g ≤ LinearMap.ker f.hom :=
    iSup_le fun g ↦ LinearMap.range_le_ker_iff.2 congr(($(hf (ModuleCat.ofHom g))).hom)
  rw [Module.IsGenerator.iSup_range_eq_top, top_le_iff, LinearMap.ker_eq_top] at h
  exact ModuleCat.hom_ext h

/-- **A separator is a generator** of `ModuleCat R`: the quotient map from `R` by the trace ideal of
`M` vanishes on every morphism out of `M`, so the trace ideal is `R`. The modules may live in any
universe in which `R` is small. -/
theorem isGenerator_of_isSeparator [Small.{v} R] {M : ModuleCat.{v} R} (hM : IsSeparator M) :
    Module.IsGenerator R M := by
  rw [Module.isGenerator_iff_iSup_range_eq_top]
  set τ := ⨆ φ : M →ₗ[R] R, LinearMap.range φ
  have : Small.{v} (R ⧸ τ) := small_of_surjective τ.mkQ_surjective
  let e := Shrink.linearEquiv.{v} R R
  let e' := Shrink.linearEquiv.{v} R (R ⧸ τ)
  -- The quotient map `R ⟶ R ⧸ τ`, transported to the universe `v`.
  let π : ModuleCat.of R (Shrink.{v} R) ⟶ ModuleCat.of R (Shrink.{v} (R ⧸ τ)) :=
    ModuleCat.ofHom (e'.symm.toLinearMap ∘ₗ τ.mkQ ∘ₗ e.toLinearMap)
  have hπ : π = 0 := (Preadditive.isSeparator_iff _).1 hM π fun g ↦ by
    ext x
    have hx : (Submodule.Quotient.mk (e (g.hom x)) : R ⧸ τ) = 0 :=
      (Submodule.Quotient.mk_eq_zero τ).2 (Submodule.mem_iSup_of_mem (e.toLinearMap ∘ₗ g.hom)
        (LinearMap.mem_range_self (e.toLinearMap ∘ₗ g.hom) x))
    simp [π, hx]
  refine eq_top_iff.2 fun r _ ↦ (Submodule.Quotient.mk_eq_zero τ).1 (e'.symm.map_eq_zero_iff.1 ?_)
  simpa [π] using congr(($hπ).hom (e.symm r))

/-- **The separators of `ModuleCat R` are the generators**, in any universe in which `R` is
small. -/
theorem isSeparator_iff_isGenerator [Small.{v} R] (M : ModuleCat.{v} R) :
    IsSeparator M ↔ Module.IsGenerator R M :=
  ⟨isGenerator_of_isSeparator, fun _ ↦ isSeparator_of_isGenerator M⟩

/-- **A finitely generated projective module is a retract of a finite power of a generator.** -/
theorem exists_retract_pi_of_isGenerator_of_projective (M Q : ModuleCat.{v} R)
    [Module.IsGenerator R M] [Module.Finite R Q] [Module.Projective R Q] :
    ∃ n : ℕ, Nonempty (Retract Q (ModuleCat.of R (Fin n → M))) := by
  obtain ⟨n, f, g, -, -, hfg⟩ :=
    Module.IsGenerator.exists_comp_eq_id_of_projective (R := R) (M := M) Q
  exact ⟨n, ⟨⟨ModuleCat.ofHom g, ModuleCat.ofHom f, ModuleCat.hom_ext hfg⟩⟩⟩

/-- **A finitely generated projective module is a retract of a finite free module** `Rⁿ`. -/
theorem exists_retract_pi_of_projective (Q : ModuleCat.{u} R) [Module.Finite R Q]
    [Module.Projective R Q] : ∃ n : ℕ, Nonempty (Retract Q (ModuleCat.of R (Fin n → R))) :=
  exists_retract_pi_of_isGenerator_of_projective (ModuleCat.of R R) Q

end ModuleCat

namespace CategoryTheory.Equivalence

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B)

/-- An equivalence of module categories carries the regular module to a generator, the image of a
separator being a separator. -/
instance isGenerator_functor_obj_self : Module.IsGenerator B (e.functor.obj (ModuleCat.of A A)) :=
  have := ModuleCat.isGenerator_of_isSeparator ((ModuleCat.isSeparator.{u} A).of_equivalence e)
  .of_linearEquiv (e.functor.mapIso (Shrink.linearEquiv.{u} A A).toModuleIso).symm.toLinearEquiv

end CategoryTheory.Equivalence
