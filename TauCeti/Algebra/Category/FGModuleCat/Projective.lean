/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Shrink

/-!
# Projective finite-dimensional modules

Over a division ring, every finite-dimensional module is free and hence projective. Consequently,
every short exact sequence of finite-dimensional modules splits.

## Main results

* `FGModuleCat.projective`: every finite-dimensional module over a division ring is projective.
* `FGModuleCat.projective_of_moduleProjective`: every finitely generated projective module is a
  projective object.
* `FGModuleCat.projective_of_free`: every finite free module is projective.
* `FGModuleCat.enoughProjectives`: every finitely generated module is a quotient of a finite free
  module.
* `FGModuleCat.moduleProjective_of_projective`: a projective object of `FGModuleCat R` is a
  projective `R`-module, provided `R` is small relative to the universe of the modules.
* `FGModuleCat.nonempty_splitting_of_shortExact`: every short exact sequence of finite-dimensional
  modules over a division ring splits.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable (R : Type u) [Ring R]

/-- A finitely generated projective module is a projective object of `FGModuleCat R`. -/
theorem _root_.FGModuleCat.projective_of_moduleProjective (X : FGModuleCat.{v} R)
    [Module.Projective R X] : Projective X := by
  apply (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).projective_of_map_projective
  have hP : Module.Projective R X.obj := inferInstanceAs (Module.Projective R X)
  exact @ModuleCat.projective_of_categoryTheory_projective R _ X.obj hP

/-- Every finite free module is a projective object. -/
theorem _root_.FGModuleCat.projective_of_free (X : FGModuleCat.{v} R) [Module.Free R X] :
    Projective X := by
  let _ : Module.Projective R X := Module.Projective.of_basis (Module.Free.chooseBasis R X)
  exact FGModuleCat.projective_of_moduleProjective R X

variable {R} in
/-- A projective object among the finitely generated modules is projective as an `R`-module. The
smallness hypothesis holds automatically when the modules live in a universe containing `R`. -/
theorem _root_.FGModuleCat.moduleProjective_of_projective [Small.{v} R]
    (X : FGModuleCat.{v} R) [Projective X] : Module.Projective R X := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R X
  let e := Shrink.linearEquiv.{v} R (Fin n → R)
  let p : FGModuleCat.of R (Shrink.{v} (Fin n → R)) ⟶ X := FGModuleCat.ofHom (f ∘ₗ e.toLinearMap)
  let _ : Epi p := ConcreteCategory.epi_of_surjective p (hf.comp e.surjective)
  let s := Projective.factorThru (𝟙 X) p
  apply Module.Projective.of_split s.hom.hom p.hom.hom
  apply LinearMap.ext
  intro x
  exact congrArg (fun g : X ⟶ X ↦ g.hom.hom x) (Projective.factorThru_comp (𝟙 X) p)

variable {R} in
/-- `FGModuleCat R` has enough projectives: every finitely generated module is a quotient of a
finite free module. The smallness hypothesis holds automatically when the modules live in a
universe containing `R`. -/
instance _root_.FGModuleCat.enoughProjectives [Small.{v} R] :
    EnoughProjectives (FGModuleCat.{v} R) where
  presentation X := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R X
    let e := Shrink.linearEquiv.{v} R (Fin n → R)
    let _ : Module.Free R (Shrink.{v} (Fin n → R)) := .of_equiv e.symm
    exact ⟨{
      p := FGModuleCat.of R (Shrink.{v} (Fin n → R))
      projective := FGModuleCat.projective_of_free R _
      f := FGModuleCat.ofHom (f ∘ₗ e.toLinearMap)
      epi := ConcreteCategory.epi_of_surjective _ (hf.comp e.surjective) }⟩

variable (k : Type u) [DivisionRing k]

/-- Every finite-dimensional vector space over a division ring is a projective object. -/
theorem _root_.FGModuleCat.projective (X : FGModuleCat.{v} k) : Projective X :=
  FGModuleCat.projective_of_free k X

/-- Every short exact sequence of finite-dimensional vector spaces over a division ring splits. -/
theorem _root_.FGModuleCat.nonempty_splitting_of_shortExact
    {S : ShortComplex (FGModuleCat.{v} k)}
    (hS : S.ShortExact) : Nonempty S.Splitting := by
  have h₃ : (ExactStructure.abelian (FGModuleCat.{v} k)).isProjective S.X₃ :=
    (ExactStructure.abelian_isProjective_iff S.X₃).mpr (FGModuleCat.projective k S.X₃)
  exact ⟨(ExactStructure.abelian (FGModuleCat.{v} k)).splittingOfProjective
    ((ExactStructure.abelian_conflation S).mpr hS) h₃⟩

end TauCeti
