/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct

/-!
# Cohomology of the trivial line bundle and the structure sheaf

The trivial line bundle is constructed as the free sheaf on one generator. This file records the
canonical base-linear comparison between its cohomology and the cohomology of the structure sheaf,
and shows that on a nonempty scheme `H⁰(X, 𝒪_X)` has rank one over the global functions
(`AlgebraicGeometry.Scheme.Modules.finrank_globalSections_cohomology_zero_trivial_eq_one`).
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
      (InvertibleSheaf.trivialObjIsoUnit X) i

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.trivialCohomologyBaseLinearEquiv_apply (i : ℕ)
    (x : Cohomology (InvertibleSheaf.trivial X).obj i) :
    trivialCohomologyBaseLinearEquiv R X i x =
      cohomologyMapBaseLinear R X (InvertibleSheaf.trivialObjIsoUnit X).hom i x := by
  dsimp [trivialCohomologyBaseLinearEquiv]
  exact cohomologyBaseLinearEquivOfIso_apply R _ i x

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.trivialCohomologyBaseLinearEquiv_symm_apply (i : ℕ)
    (x : Cohomology (SheafOfModules.unit X.ringCatSheaf : X.Modules) i) :
    (trivialCohomologyBaseLinearEquiv R X i).symm x =
      cohomologyMapBaseLinear R X (InvertibleSheaf.trivialObjIsoUnit X).inv i x := by
  dsimp [trivialCohomologyBaseLinearEquiv]
  exact cohomologyBaseLinearEquivOfIso_symm_apply R _ i x

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

/-- On a nonempty scheme, `H⁰(X, 𝒪_X)` is free of rank one over the ring `Γ(X, 𝒪_X)` of global
functions: it is identified with `Γ(X, 𝒪_X)` itself. -/
@[simp]
theorem finrank_globalSections_cohomology_zero_trivial_eq_one {X : Scheme.{u}} [Nonempty X] :
    Module.finrank Γ(X, ⊤) (Cohomology (InvertibleSheaf.trivial X).obj 0) = 1 := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : (InvertibleSheaf.trivial X).obj ≅ M :=
    eqToIso (InvertibleSheaf.trivial_obj X) ≪≫ TauCeti.SheafOfModules.freePUnitIsoUnit _
  let f : Cohomology (InvertibleSheaf.trivial X).obj 0 ≃ₗ[Γ(X, ⊤)] Cohomology M 0 :=
    .ofLinearMap (cohomologyMapLinear e.hom 0) (cohomologyMapLinear e.inv 0)
      (by rw [← cohomologyMapLinear_comp, e.inv_hom_id, cohomologyMapLinear_id])
      (by rw [← cohomologyMapLinear_comp, e.hom_inv_id, cohomologyMapLinear_id])
  rw [f.finrank_eq, (cohomologyZeroLinearEquiv M).finrank_eq]
  -- The global sections of the structure sheaf, as a module over the global functions, are the
  -- global functions acting on themselves.
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nontrivial Γ(X, ⊤) := X.component_nontrivial ⊤
  exact Module.finrank_self Γ(X, ⊤)

end AlgebraicGeometry.Scheme.Modules
