/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Finite pushforward of module sheaves

Pushforward along a finite morphism preserves coherent sheaves when the target is locally
Noetherian, and preserves finitely presented sheaves over an arbitrary base when the morphism is
also locally of finite presentation. This permits coherent coefficients on a closed subscheme to be
viewed as coherent coefficients on its ambient scheme, and makes the coordinate algebra of any
finite locally finitely presented morphism finitely presented as an `𝒪_Y`-module.

The affine calculation uses the existing quasi-coherent pushforward theorem and the
tilde/global-sections comparison. A finite module over a finite algebra is finite over the
base ring; over a Noetherian base this gives a finite presentation, while for a finite locally
finitely presented morphism a finitely presented module over a finitely presented finite algebra is
finitely presented over the base ring.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.5.
* The Stacks Project, Tag 01Y6 (coherent pushforward along finite morphisms) and Tag 0564
  (transitivity of finite presentation along finite finitely presented ring maps).
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
    ((pushforward f).obj M).IsFinitePresentation :=
  isFinitePresentation_of_finitePresentation_sections _ fun U hU ↦ by
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have := M.finite_sections_pushforward f U hU
    exact Module.finitePresentation_of_finite _ _

/-- Over an affine open, the pushforward of a finitely presented module along a finite morphism
locally of finite presentation has finitely presented sections, without any Noetherian
hypothesis. -/
theorem finitePresentation_sections_pushforward (M : X.Modules) [M.IsFinitePresentation]
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f] (U : Y.Opens)
    (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(Y, U) Γ((pushforward f).obj M, U) := by
  have hfp := f.finitePresentation_appLE hU (hU.preimage f) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hfp
  have hfin := f.finite_app U hU
  algebraize [(f.app U).hom]
  have : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    Module.FinitePresentation.of_finite_of_finitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U)
  have : Module.FinitePresentation Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U) :=
    M.finitePresentation_sections_of_isAffineOpen _ (hU.preimage f)
  let : Module Γ(Y, U) Γ(M, f ⁻¹ᵁ U) := Module.compHom Γ(M, f ⁻¹ᵁ U) (f.app U).hom
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U) :=
    ⟨fun r s m ↦ mul_smul ((f.app U).hom r) s m⟩
  -- Pushforward sections are `Γ(M, f ⁻¹ᵁ U)` with scalars restricted along `(f.app U).hom`.
  have hYM : Module.FinitePresentation Γ(Y, U) Γ(M, f ⁻¹ᵁ U) :=
    Module.FinitePresentation.trans Γ(Y, U) Γ(M, f ⁻¹ᵁ U) Γ(X, f ⁻¹ᵁ U)
  exact hYM

/-- Pushforward along a finite morphism locally of finite presentation preserves finite
presentation on an arbitrary scheme. -/
instance isFinitePresentation_pushforward_of_locallyOfFinitePresentation
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation :=
  isFinitePresentation_of_finitePresentation_sections _
    (M.finitePresentation_sections_pushforward f)

end AlgebraicGeometry.Scheme.Modules
