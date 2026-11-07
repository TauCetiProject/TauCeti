/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Base-ring actions on scheme-module stalks

For a scheme over `Spec R`, each module stalk is an `R`-module through the canonical
map `R → 𝒪_{X,x}`. These actions are compatible with both the local-ring action and
the section-ring action on a neighbourhood of the point.

This file combines the module-stalk structures with the scheme's base-algebra
structures without imposing the latter dependencies on `Modules.Stalk`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Base

variable {X : Scheme.{u}} (M : X.Modules) (x : X)
  (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- A module stalk on a scheme over `Spec R` is an `R`-module through the local ring. -/
instance (priority := 900) stalkBaseModule : Module R (M.presheaf.stalk x) :=
  Module.compHom _ (X.baseRingToStalk R x)

/-- The base-ring action on a module stalk factors through its local ring. -/
instance isScalarTower_baseStalk :
    IsScalarTower R (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  IsScalarTower.of_compHom _ _ _

@[simp]
lemma base_smul_stalk_def (r : R) (m : M.presheaf.stalk x) :
    r • m = X.baseRingToStalk R x r • m :=
  (rfl)

/-- The base-ring and section-ring actions on a module stalk agree. -/
lemma isScalarTower_base_section_moduleStalk {U : X.Opens} (x : U) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    IsScalarTower R Γ(X, U) (M.presheaf.stalk x) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  have := X.isScalarTower_base_section_stalk R x
  exact IsScalarTower.of_algebraMap_smul fun r m ↦ by
    rw [base_smul_stalk_def]
    exact congrArg (· • m)
      (IsScalarTower.algebraMap_apply R Γ(X, U) (X.presheaf.stalk x) r).symm

end Base

end AlgebraicGeometry.Scheme.Modules
