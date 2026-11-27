/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.CategoryTheory.Abelian.Injective.Basic

/-!
# Dual short exact sequences of right modules

Matlis duality with injective coefficients sends a short exact sequence of right modules to a
short exact sequence of left modules, reversing its two maps.
-/

public section

open CategoryTheory TauCeti

namespace CategoryTheory.ShortComplex

universe u v w t

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]
  {A : Type w} [Ring A] [Algebra R A] {S : ShortComplex (ModuleCat.{max v t} Aᵐᵒᵖ)}

/-- Matlis duality with injective coefficients takes short exact sequences of right modules to
short exact sequences of left modules. -/
theorem ShortExact.matlisDualOp [Small.{v} R] [Module.Injective R E] (hS : S.ShortExact) :
    (S.op.map (ModuleCat.matlisDualOp R E)).ShortExact := by
  let F := ModuleCat.restrictScalars.{max v t} (algebraMap R Aᵐᵒᵖ)
  let J := ModuleCat.of R (ULift.{t} E)
  let G := preadditiveYonedaObj J
  have : Module.Injective R (ULift.{t} E) := Module.ulift_injective_of_injective R inferInstance
  have : Injective J := Module.injective_object_of_injective_module R (ULift.{t} E)
  have := G.preservesFiniteLimits_of_preservesHomology
  have hT := (hS.map_of_exact F).op.map_of_exact G
  let e (N : ModuleCat.{max v t} Aᵐᵒᵖ) :
      ModuleCat.matlisDualOpObj R E N ≃+ (F.obj N ⟶ J) :=
    (ModuleCat.matlisDualOpObjEquiv R E N).toAddEquiv.trans
      ((MatlisDual.equivLinearMap R E N).toAddEquiv.trans
        ((LinearEquiv.arrowCongr (LinearEquiv.refl R N) ULift.moduleEquiv.symm).toAddEquiv.trans
          (ModuleCat.homAddEquiv (R := R) (M := F.obj N) (N := J)).symm))
  have hmap {N N' : ModuleCat.{max v t} Aᵐᵒᵖ} (f : N ⟶ N')
      (φ : ModuleCat.matlisDualOpObj R E N') :
      e N ((ModuleCat.matlisDualOpMap R E f).hom φ) = (G.map (F.map f).op).hom (e N' φ) := by
    ext x
    -- Evaluation of a Yoneda map is precomposition followed by evaluation in the lift.
    change ((MatlisDual.equivLinearMap R E N) (ModuleCat.matlisDualOpObjEquiv R E N
      (ModuleCat.matlisDualOpMap R E f φ))) x =
      ((MatlisDual.equivLinearMap R E N') (ModuleCat.matlisDualOpObjEquiv R E N' φ)) (f x)
    exact ModuleCat.matlisDualOpObjEquiv_map_apply R E f φ x
  have hex : Function.Exact (G.map (F.map S.g).op).hom (G.map (F.map S.f).op).hom :=
    (ShortExact.moduleCat_exact_iff_function_exact _).mp hT.exact
  have hi : Function.Injective (G.map (F.map S.g).op).hom := hT.moduleCat_injective_f
  have hs : Function.Surjective (G.map (F.map S.f).op).hom := hT.moduleCat_surjective_g
  have hd : Function.Exact (ModuleCat.matlisDualOpMap R E S.g).hom
      (ModuleCat.matlisDualOpMap R E S.f).hom :=
    Function.Exact.of_ladder_addEquiv_of_exact' (e S.X₃) (e S.X₂) (e S.X₁)
      (f₁₂ := (ModuleCat.matlisDualOpMap R E S.g).hom.toAddMonoidHom)
      (f₂₃ := (ModuleCat.matlisDualOpMap R E S.f).hom.toAddMonoidHom)
      (g₁₂ := (G.map (F.map S.g).op).hom.toAddMonoidHom)
      (g₂₃ := (G.map (F.map S.f).op).hom.toAddMonoidHom)
      (AddMonoidHom.ext fun x ↦ (hmap S.g x).symm)
      (AddMonoidHom.ext fun x ↦ (hmap S.f x).symm) hex
  have hdi : Function.Injective (ModuleCat.matlisDualOpMap R E S.g).hom := by
    intro x y h
    apply (e S.X₃).injective
    exact hi ((hmap S.g x).symm.trans ((congrArg (e S.X₂) h).trans (hmap S.g y)))
  have hds : Function.Surjective (ModuleCat.matlisDualOpMap R E S.f).hom := by
    intro y
    obtain ⟨x, hx⟩ := hs (e S.X₁ y)
    refine ⟨(e S.X₂).symm x, (e S.X₁).injective ?_⟩
    exact (hmap _ _).trans ((congrArg _ ((e S.X₂).apply_symm_apply x)).trans hx)
  -- The functor on the opposite complex uses the bundled dual maps.
  exact ModuleCat.shortComplex_shortExact _ hd hdi hds

end CategoryTheory.ShortComplex
