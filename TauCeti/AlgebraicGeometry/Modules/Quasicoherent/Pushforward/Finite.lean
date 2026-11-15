/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Finite pushforward of module sheaves

Pushforward along a finite morphism preserves finitely presented sheaves in two settings:

* when the target scheme is locally Noetherian and the source module is quasi-coherent of finite
  type (`isFinitePresentation_pushforward_of_isFinite`, Stacks Tag 01Y6);
* without any Noetherian hypothesis, when the finite morphism is locally of finite presentation and
  the source module is of finite presentation
  (`isFinitePresentation_pushforward_of_isFinite_of_locallyOfFinitePresentation`, Stacks Tag 0564),
  in particular for finite étale morphisms and for their structure sheaves.

Both reduce to sections over affine opens `U ⊆ Y` via
`isFinitePresentation_of_finitePresentation_sections`. Over a locally Noetherian target, a finite
module over a finite algebra is finite over the Noetherian base ring and hence finitely presented.
Over a general target, a finite algebra of finite presentation is finitely presented as a module
(`Module.FinitePresentation.of_finite_of_finitePresentation`), and finite presentation of modules is
transitive along restriction of scalars (`Module.FinitePresentation.trans`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.finite_sections_pushforward`: sections of a finite pushforward
  of a finite-type quasi-coherent module over an affine open form a finite module.
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_of_isFinite`: finite
  pushforward onto a locally Noetherian target sends finite-type quasi-coherent modules to finitely
  presented modules.
* `AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_pushforward` and
  `isFinitePresentation_pushforward_of_isFinite_of_locallyOfFinitePresentation`:
  pushforward along a finite morphism locally of finite presentation preserves finite presentation
  without Noetherian hypotheses (Stacks, Lemma 29.21.12 (0564)).

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.5.
* The Stacks Project, Tag 01Y6 (coherent pushforward along finite morphisms) and
  Lemma 29.21.12 (Tag 0564, finite presentation under finite finitely presented pushforward).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The sections of a finite pushforward over an affine open form a finite module if the
original sheaf is quasi-coherent and of finite type. No Noetherian hypothesis is needed. -/
theorem finite_sections_pushforward (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (f : X ⟶ Y) [IsFinite f] (U : Y.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(Y, U) Γ((pushforward f).obj M, U) := by
  -- Pushforward sections are the restriction of scalars of the preimage sections
  -- along `f.app U`, definitionally as objects of `ModuleCat`.
  exact (ModuleCat.isFG_iff _).mp
    ((f.app U).hom.isFG_restrictScalars_of_finite (f.finite_app U hU)
      ((ModuleCat.isFG_iff _).mpr (M.finite_sections_of_isAffineOpen _ (hU.preimage f))))

/-- Finite pushforward on a locally Noetherian target preserves finite presentation.
It suffices that the source coefficient is quasi-coherent and of finite type. -/
instance isFinitePresentation_pushforward_of_isFinite [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pushforward f).obj M).IsFinitePresentation := by
  refine isFinitePresentation_of_finitePresentation_sections _ fun U hU ↦ ?_
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(Y, U) Γ((pushforward f).obj M, U) := M.finite_sections_pushforward f U hU
  exact Module.finitePresentation_of_finite _ _

/-- Over an affine open, the sections of the pushforward of a finitely presented module along a
finite morphism locally of finite presentation form a finitely presented module. No Noetherian
hypothesis is needed. -/
@[stacks 0564]
theorem finitePresentation_sections_pushforward (M : X.Modules) [M.IsFinitePresentation]
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f] (U : Y.Opens) (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(Y, U) Γ((pushforward f).obj M, U) := by
  have hfp_hom : (f.app U).hom.FinitePresentation := by
    rw [f.app_eq_appLE]
    exact f.finitePresentation_appLE hU (hU.preimage f) le_rfl
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have : Algebra.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := hfp_hom
  have : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    Module.FinitePresentation.of_finite_of_finitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
  have : Module.FinitePresentation Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U) :=
    M.finitePresentation_sections_of_isAffineOpen _ (hU.preimage f)
  let : Module Γ(Y, U) Γ(M, f ⁻¹ᵁ U) :=
    Module.compHom _ (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U))
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U) :=
    ⟨fun r s m ↦ mul_smul (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U) r) s m⟩
  have : Module.FinitePresentation Γ(Y, U) Γ(M, f ⁻¹ᵁ U) :=
    Module.FinitePresentation.trans Γ(Y, U) Γ(M, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ U)
  exact Module.FinitePresentation.of_equiv
    (ModuleCat.restrictScalarsAlgebraMapIso (R := Γ(Y, U)) (S := Γ(X, f ⁻¹ᵁ U))
      Γ(M, f ⁻¹ᵁ U)).symm.toLinearEquiv

/-- Pushforward along a finite morphism locally of finite presentation preserves finite
presentation, without any Noetherian hypothesis. Stacks, Lemma 29.21.12 (0564). -/
@[stacks 0564]
instance isFinitePresentation_pushforward_of_isFinite_of_locallyOfFinitePresentation
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation := by
  have : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  exact isFinitePresentation_of_finitePresentation_sections _
    (M.finitePresentation_sections_pushforward f)

end AlgebraicGeometry.Scheme.Modules
