/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Dual short exact sequences of right modules

Matlis duality with injective coefficients sends a short exact sequence of right modules to a
short exact sequence of left modules, reversing its two maps.
-/

public section

open CategoryTheory TauCeti

namespace ModuleCat

universe u v w t

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra

/-- On underlying additive groups, Matlis duality is Yoneda into the lifted coefficient module
following restriction of scalars. -/
noncomputable def matlisDualOpForgetIsoYoneda (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E] {A : Type w} [Ring A] [Algebra R A] :
    matlisDualOp R E (A := A) ⋙ forget₂ (ModuleCat.{max v t} A) AddCommGrpCat ≅
      (restrictScalars.{max v t} (algebraMap R Aᵐᵒᵖ)).op ⋙
        preadditiveYonedaObj (ModuleCat.of R (ULift.{t} E)) ⋙
          forget₂ _ AddCommGrpCat := by
  let F := restrictScalars.{max v t} (algebraMap R Aᵐᵒᵖ)
  let J := ModuleCat.of R (ULift.{t} E)
  let e (N : ModuleCat.{max v t} Aᵐᵒᵖ) :
      matlisDualOpObj R E N ≃+ (F.obj N ⟶ J) :=
    (matlisDualOpObjEquiv R E N).toAddEquiv.trans
      ((MatlisDual.equivLinearMap R E N).toAddEquiv.trans
        ((LinearEquiv.arrowCongr (LinearEquiv.refl R N) ULift.moduleEquiv.symm).toAddEquiv.trans
          (homAddEquiv (R := R) (M := F.obj N) (N := J)).symm))
  refine NatIso.ofComponents (fun N ↦ (e N.unop).toAddCommGrpIso) ?_
  intro N N' f
  apply AddCommGrpCat.ext
  intro φ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  -- Yoneda precomposition evaluates the same functional at the same module element.
  change ((MatlisDual.equivLinearMap R E N'.unop) (matlisDualOpObjEquiv R E N'.unop
    (matlisDualOpMap R E f.unop φ))) x =
    ((MatlisDual.equivLinearMap R E N.unop) (matlisDualOpObjEquiv R E N.unop φ)) (f.unop x)
  exact matlisDualOpObjEquiv_map_apply R E f.unop φ x

/-- The Matlis--Yoneda comparison sends a functional to its lift-valued module morphism. -/
theorem matlisDualOpForgetIsoYoneda_hom_app_apply (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E] {A : Type w} [Ring A] [Algebra R A]
    (N : ModuleCat.{max v t} Aᵐᵒᵖ) (φ : matlisDualOpObj R E N) :
    (matlisDualOpForgetIsoYoneda.{u, v, w, t} R E).hom.app (Opposite.op N) φ =
      ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
        MatlisDual.equivLinearMap R E N (matlisDualOpObjEquiv R E N φ)) := by
  rfl

end ModuleCat

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
  let H := forget₂ (ModuleCat.{max v t} A) AddCommGrpCat
  let e := ModuleCat.matlisDualOpForgetIsoYoneda R E (A := A)
  let i : ((S.op.map (ModuleCat.matlisDualOp R E)).map H) ≅
      (((S.map F).op.map G).map (forget₂ _ AddCommGrpCat)) :=
    isoMk (e.app (Opposite.op S.X₃)) (e.app (Opposite.op S.X₂))
      (e.app (Opposite.op S.X₁))
      (e.hom.naturality S.g.op).symm
      (e.hom.naturality S.f.op).symm
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful H
    (shortExact_of_iso i.symm (hT.map_of_exact (forget₂ _ AddCommGrpCat)))

end CategoryTheory.ShortComplex
