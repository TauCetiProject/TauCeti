/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.RingTheory.Flat.TensorProduct
public import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness of sections over affine opens

For a quasi-coherent module on a scheme over `Spec R`, flatness over `R` of the
sections on an affine open is equivalent to flatness over `R` of all stalks on that
open. In particular, a sheaf flat over the base has flat modules of sections on
affine opens. No flatness of the scheme over the base, finiteness, or Noetherian
hypothesis is needed.

This is the geometric input for constructing flat Čech complexes used in cohomology
and base change. The base action on a stalk is through the canonical map
`R → 𝒪_{X,x}`; localization at the image point of `Spec R` gives the usual
relative-flatness condition. This file also provides that base-ring action and its
compatibility with the local-ring and section-ring actions.

## References

* The Stacks Project, Section 17.17 (Tag 05NC), flat modules on ringed spaces.
* R. Hartshorne, *Algebraic Geometry*, III, Proposition 12.2.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

attribute [local instance] AlgebraicGeometry.Scheme.Modules.sectionsBaseModule

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

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  (M : X.Modules) {U : X.Opens}

/-- Flat sections of a quasi-coherent sheaf on an affine open have flat stalks there,
even when the affine coordinate ring is not flat over the base. -/
theorem flat_stalk_of_flat_sections [M.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Flat R Γ(M, U)] (x : U) : Module.Flat R (M.presheaf.stalk x) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  have : IsScalarTower R Γ(X, U) Γ(M, U) := IsScalarTower.of_compHom _ _ _
  have := X.isScalarTower_base_section_stalk R x
  have := M.isScalarTower_base_section_moduleStalk R x
  have := hU.isLocalization_stalk x
  have := IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal.primeCompl
  have := Module.Flat.tensorProduct_of_flat (R := R) (B := Γ(X, U))
    (M := Γ(M, U)) (X.presheaf.stalk x)
  exact Module.Flat.of_linearEquiv ((M.isBaseChange_germₗ x hU).equiv.restrictScalars R).symm

/-- If every stalk on an affine open is flat over the base ring, its sections are flat
over the base ring. Quasi-coherence is essential for identifying stalks with localizations. -/
theorem flat_sections_of_flat_stalk [M.IsQuasicoherent] (hU : IsAffineOpen U)
    (hM : ∀ x : U, Module.Flat R (M.presheaf.stalk x)) : Module.Flat R Γ(M, U) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  have : IsScalarTower R Γ(X, U) Γ(M, U) := IsScalarTower.of_compHom _ _ _
  let x (P : Ideal Γ(X, U)) [P.IsMaximal] : U := hU.isoSpec.inv ⟨P, inferInstance⟩
  have hx (P : Ideal Γ(X, U)) [P.IsMaximal] : (hU.primeIdealOf (x P)).asIdeal = P := by
    exact congrArg PrimeSpectrum.asIdeal (Scheme.inv_hom_apply hU.isoSpec ⟨P, inferInstance⟩)
  have hTower : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal],
      IsScalarTower R Γ(X, U) (M.presheaf.stalk (x P)) :=
    fun P _ ↦ M.isScalarTower_base_section_moduleStalk R (x P)
  have hloc : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal],
      IsLocalizedModule.AtPrime P (M.germₗ (x P)) := fun P _ ↦ by
    simpa only [hx P] using M.isLocalizedModule_germₗ (x P) hU
  -- Specify the actions on this dependent family: instance inference cannot recover
  -- the affine neighbourhood from the underlying points of its stalks.
  exact @Module.flat_of_isLocalized_maximal R Γ(X, U) _ _ _ Γ(M, U) _ _ _
    inferInstance (fun P _ ↦ M.presheaf.stalk (x P)) _
    (fun P _ ↦ M.stalkBaseModule (x P) R) (fun P _ ↦ M.moduleSectionStalk (x P))
    hTower (fun P _ ↦ M.germₗ (x P)) hloc (fun P _ ↦ hM (x P))

/-- Over an affine open, flatness of sections is equivalent to flatness of all stalks
over the base ring. -/
theorem flat_sections_iff [M.IsQuasicoherent] (hU : IsAffineOpen U) :
    Module.Flat R Γ(M, U) ↔ ∀ x : U, Module.Flat R (M.presheaf.stalk x) :=
  ⟨fun _ x ↦ flat_stalk_of_flat_sections R M hU x, flat_sections_of_flat_stalk R M hU⟩

end AlgebraicGeometry.Scheme.Modules
