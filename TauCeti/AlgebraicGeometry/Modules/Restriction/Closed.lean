/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Restriction.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Closed.Functor
import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Closed
import TauCeti.CategoryTheory.Monoidal.Closed.Equivalence
import TauCeti.CategoryTheory.Monoidal.Closed.Naturality

/-!
# Restriction of internal Hom to an open subscheme

Restriction to an open subscheme commutes with internal Hom for arbitrary module sheaves.
The slice-site restriction formula transports across Mathlib's `Scheme.Modules.overEquiv`,
whose tensor comparison is invertible. Its compatibility with the ordinary restriction
functor identifies the resulting isomorphism with the canonical internal-Hom comparison.

No quasicoherence, finiteness, or local freeness is required.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- The tensor product used by the internal-Hom category on the slice over `U`. -/
local instance monoidalCategoryRestrictionClosed :
    MonoidalCategory (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  TauCeti.SheafOfModules.monoidalCategory (X.sheaf.over U)

/-- The tensor--Hom adjunction for module sheaves on the slice over `U`. -/
local instance monoidalClosedRestrictionClosed :
    MonoidalClosed (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  TauCeti.SheafOfModules.monoidalClosed (X.sheaf.over U)

/-- Restriction to an open subscheme preserves internal Hom for arbitrary module sheaves. -/
instance isIso_restrictFunctor_ihomComparison_app (M N : X.Modules) :
    IsIso (((restrictFunctor U.ι).ihomComparison M).app N) := by
  -- Preserve the scheme-module structures when the source is written as sheaves of modules.
  let : MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
    Scheme.Modules.instMonoidalCategory X
  let : MonoidalClosed (SheafOfModules.{u} X.ringCatSheaf) :=
    Scheme.Modules.instMonoidalClosed X
  let F : X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
    SheafOfModules.overFunctor X.ringCatSheaf U
  let : F.Monoidal := SheafOfModules.overFunctorMonoidal (R := X.sheaf) (X := U)
  let G := (overEquiv U).functor
  have hG : IsIso (G.ihomComparison (F.obj M)) :=
    G.ihomComparison_isIso_of_equivalence (F.obj M)
  have : IsIso (M.overIhomComparison X.sheaf U) :=
    SheafOfModules.isIso_overIhomComparison (R := X.sheaf) (X := U) M
  have hF : IsIso ((F.ihomComparison M).app N) := by
    have h := (NatTrans.isIso_iff_isIso_app (M.overIhomComparison X.sheaf U)).mp ‹_› N
    have heq := congrArg (fun α ↦ α.app N)
      (SheafOfModules.overIhomComparison_def (R := X.sheaf) (X := U) (M := M))
    exact (congrArg IsIso heq).mp h
  have hFG : IsIso (((F ⋙ G).ihomComparison M).app N) := by
    rw [Functor.ihomComparison_comp]
    infer_instance
  have hμ := overFunctorEquiv_hom_tensor U M ((ihom (C := X.Modules) M).obj N)
  let cm : Closed (C := X.Modules) M := inferInstance
  -- Specify the scheme-module structures explicitly at the slice-to-scheme boundary.
  exact (@Functor.isIso_ihomComparison_app_iff_of_natIso
    X.Modules _ (Scheme.Modules.instMonoidalCategory X)
    (U : Scheme).Modules _ (Scheme.Modules.instMonoidalCategory (U : Scheme))
    (F ⋙ G) (restrictFunctor U.ι) _ _ (overFunctorEquiv U) M N cm
    inferInstance inferInstance hμ).mp hFG

end AlgebraicGeometry.Scheme.Modules

end
