/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Trivial
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

/-!
# Zeroth cohomology of the structure sheaf of an affine scheme

Let `A` be an algebra over a commutative ring `R`, and regard `Spec A` as a scheme over `Spec R`
through Mathlib's instance `AlgebraicGeometry.specOverSpec`. This file identifies the zeroth
cohomology of the structure sheaf of `Spec A` with `A`, as `R`-modules
(`TauCeti.AlgebraicGeometry.cohomologyZeroTrivialSpecLinearEquiv`). The higher cohomology of the
structure sheaf vanishes by Serre's vanishing theorem on affine schemes
(`AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isAffine`).

So finiteness or flatness over `R` of the cohomology of the structure sheaf of `Spec A` is
finiteness or flatness of `A` itself. For instance `H⁰(Spec R[t], 𝒪)` is not a finite `R`-module
when `R` is nonzero: the finiteness of cohomology of coherent sheaves needs properness.

The identification is the composite of the identification of zeroth cohomology with global
sections, as modules over the base ring (`Scheme.Modules.cohomologyZeroBaseLinearEquiv`), with
Mathlib's isomorphism `AlgebraicGeometry.Scheme.ΓSpecIso` between the global functions on `Spec A`
and `A`; the base ring acts compatibly on both sides
(`Scheme.baseRingToStructurePresheaf_Spec_app_apply`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition II.2.2(c) and
  Theorem III.3.5.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]

/-- **The zeroth cohomology of the structure sheaf of `Spec A` is `A`**, as modules over the base
ring `R`, where `Spec A` lies over `Spec R` through the algebra map `R → A`. -/
def cohomologyZeroTrivialSpecLinearEquiv :
    Cohomology (InvertibleSheaf.trivial (Spec A)).obj 0 ≃ₗ[R] A :=
  letI : Algebra R Γ(Spec A, ⊤) :=
    (((Spec A).baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  ((trivialCohomologyBaseLinearEquiv R _ 0).trans ((cohomologyZeroBaseLinearEquiv R _ _).trans
    (structureSheafSectionsBaseLinearEquiv R _))).trans
    (AlgEquiv.ofRingEquiv (f := (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv) fun r ↦ by
      rw [RingHom.algebraMap_toAlgebra, Scheme.baseRingToStructurePresheaf_Spec_app_apply]
      exact (Scheme.ΓSpecIso A).inv_hom_id_apply (algebraMap R A r)).toLinearEquiv

/-- Under `cohomologyZeroTrivialSpecLinearEquiv`, a cohomology class is sent to its global section,
viewed as an element of `A` through `Scheme.ΓSpecIso`. -/
@[simp]
theorem cohomologyZeroTrivialSpecLinearEquiv_apply
    (x : Cohomology (InvertibleSheaf.trivial (Spec A)).obj 0) :
    cohomologyZeroTrivialSpecLinearEquiv R A x = (Scheme.ΓSpecIso A).hom
      (cohomologyZeroBaseLinearEquiv R _ (SheafOfModules.unit (Spec A).ringCatSheaf)
        (trivialCohomologyBaseLinearEquiv R _ 0 x)) := by
  simp only [cohomologyZeroTrivialSpecLinearEquiv, LinearEquiv.trans_apply,
    structureSheafSectionsBaseLinearEquiv_apply]
  rfl

/-- Under `cohomologyZeroTrivialSpecLinearEquiv`, an element `a` of `A` is the class of the global
function on `Spec A` corresponding to `a` through `Scheme.ΓSpecIso`. -/
@[simp]
theorem cohomologyZeroTrivialSpecLinearEquiv_symm_apply (a : A) :
    (cohomologyZeroTrivialSpecLinearEquiv R A).symm a =
      (trivialCohomologyBaseLinearEquiv R _ 0).symm
        ((cohomologyZeroBaseLinearEquiv R _ (SheafOfModules.unit (Spec A).ringCatSheaf)).symm
          ((Scheme.ΓSpecIso A).inv a)) := by
  simp only [cohomologyZeroTrivialSpecLinearEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    structureSheafSectionsBaseLinearEquiv_symm_apply]
  rfl

end TauCeti.AlgebraicGeometry
