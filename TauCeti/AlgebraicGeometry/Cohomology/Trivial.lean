/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Cohomology of the trivial line bundle and the structure sheaf

The trivial line bundle is constructed as the free sheaf on one generator. This file records the
canonical base-linear comparison between its cohomology and the cohomology of the structure sheaf.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The cohomology of the trivial line bundle is base-linearly equivalent to that of the structure
sheaf. -/
def _root_.AlgebraicGeometry.Scheme.Modules.trivialCohomologyBaseLinearEquiv (i : ℕ) :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    Cohomology (InvertibleSheaf.trivial X).obj i ≃ₗ[R]
      Cohomology M i := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  exact
    cohomologyBaseLinearEquivOfIso R (M := (InvertibleSheaf.trivial X).obj)
      (N := M)
      (eqToIso (InvertibleSheaf.trivial_obj X) ≪≫
        TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf) i

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.trivialCohomologyBaseLinearEquiv_apply (i : ℕ)
    (x : Cohomology (InvertibleSheaf.trivial X).obj i) :
    trivialCohomologyBaseLinearEquiv R X i x =
      cohomologyMapBaseLinear R X
        (eqToIso (InvertibleSheaf.trivial_obj X) ≪≫
          TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).hom i x := by
  dsimp [trivialCohomologyBaseLinearEquiv]
  exact cohomologyBaseLinearEquivOfIso_apply R _ i x

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.trivialCohomologyBaseLinearEquiv_symm_apply (i : ℕ)
    (x : Cohomology (SheafOfModules.unit X.ringCatSheaf : X.Modules) i) :
    (trivialCohomologyBaseLinearEquiv R X i).symm x =
      cohomologyMapBaseLinear R X
        (eqToIso (InvertibleSheaf.trivial_obj X) ≪≫
          TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).inv i x := by
  dsimp [trivialCohomologyBaseLinearEquiv]
  exact cohomologyBaseLinearEquivOfIso_symm_apply R _ i x

end TauCeti.AlgebraicGeometry
