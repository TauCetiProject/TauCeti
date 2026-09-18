/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.SelfInjective
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Projectives over a self-injective ring

This file relates module-theoretic self-injectivity to projective and injective objects in the
category `FGModuleCat R` of finitely generated modules.

Categorical projectivity of a finitely generated module implies module-theoretic projectivity:
choose a finite free presentation and split it in `FGModuleCat R`. Consequently, when the regular
left `R`-module is injective, every projective object of `FGModuleCat R` is injective.

These results supply one direction of the projective--injective identification for the Frobenius
exact category of finite-dimensional modules over a self-injective finite-dimensional algebra.

## Main results

* `FGModuleCat.moduleProjective_of_projective`: a projective object of `FGModuleCat R` is a
  projective `R`-module.
* `FGModuleCat.injective_of_projective_of_moduleInjective_self`: over a self-injective ring, every
  projective object of `FGModuleCat R` is injective.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Sections 3 and 16.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {R : Type u} [Ring R]

namespace FGModuleCat

/-- A projective object among the finitely generated modules is projective as a module. -/
theorem moduleProjective_of_projective (X : FGModuleCat.{u} R) [Projective X] :
    Module.Projective R X := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R X
  let p : FGModuleCat.of R (Fin n → R) ⟶ X := FGModuleCat.ofHom f
  let _ : Epi p := ConcreteCategory.epi_of_surjective p hf
  let s := Projective.factorThru (𝟙 X) p
  apply Module.Projective.of_split s.hom.hom p.hom.hom
  apply LinearMap.ext
  intro x
  exact congrArg (fun g : X ⟶ X ↦ g.hom.hom x) (Projective.factorThru_comp (𝟙 X) p)

variable [IsNoetherianRing R]

/-- Over a self-injective ring, every projective object among the finitely generated modules is
injective. -/
theorem injective_of_projective_of_moduleInjective_self (hR : Module.Injective R R)
    (X : FGModuleCat.{u} R) [Projective X] : Injective X := by
  let hP : Module.Projective R X := moduleProjective_of_projective X
  let hI : Module.Injective R X := Module.Injective.of_finite_projective hR
  constructor
  intro A B f i hi
  have hi' : Function.Injective i.hom.hom := by
    let _ : Mono i.hom := (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map_mono i
    exact (ModuleCat.mono_iff_injective i.hom).mp inferInstance
  obtain ⟨g, hg⟩ := hI.out i.hom.hom hi' f.hom.hom
  exact ⟨FGModuleCat.ofHom g, FGModuleCat.hom_ext (LinearMap.ext fun x ↦ hg x)⟩

end FGModuleCat

end TauCeti
