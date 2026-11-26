/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.Condensed.Light.Solid.Basic

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.CategoryTheory.Abelian.Projective.Internal
import TauCeti.CategoryTheory.Limits.Preserves.Shapes.Kernels
import TauCeti.Condensed.Light.NullSequence.Projective

/-!
# Light solid modules form an abelian subcategory

Light solid modules are closed under kernels, cokernels, extensions and finite products. Kernels
and finite products are limits. For cokernels and extensions, internal Hom out of `nullSeq R` is
exact, because `nullSeq R` is internally projective, and the solidity test is the invertibility of
a natural endomorphism of this exact functor. The four lemma and the five lemma then transport
invertibility from the outer terms to the cokernel and to the middle of a short exact sequence.

Mathlib's `Abelian` instance on full subcategories closed under kernels, cokernels and finite
products (`Mathlib.CategoryTheory.Abelian.Subcategory`) therefore makes the light solid modules an
abelian category whose inclusion computes kernels and cokernels.

This is part of Rodríguez Camargo, *Notes on Solid Geometry*, Theorem 3.2.4, on the light site:
the closure under colimits needs more than the exactness used here.
-/

public section

universe u

open CategoryTheory Limits LightCondMod

namespace TauCeti

variable {R : Type u} [CommRing R]

/-- Solid modules are closed under kernels. -/
instance : (IsLightSolid (R := R)).IsClosedUnderKernels where
  kernels_le _ := fun ⟨_, _, hk, hX, hY⟩ ↦
    IsLightSolid.prop_of_isLimit hk (by rintro (_ | _) <;> assumption)

/-- Solid modules are closed under cokernels. -/
instance : (IsLightSolid (R := R)).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, c, hc, hX, hY⟩
    rw [isLightSolid_iff, ← lightSolidDifferenceNatTrans_app] at hX hY ⊢
    have := Functor.PreservesHomology.preservesCokernel (ihom (nullSeq R)) f
    have := Cofork.IsColimit.epi hc
    exact (lightSolidDifferenceNatTrans R).isIso_app_of_isColimit_cokernelCofork hc

/-- Solid modules are closed under extensions. -/
instance : (IsLightSolid (R := R)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have := hS.mono_f
    have := hS.epi_g
    have hF := hS.map (ihom (nullSeq R))
    rw [isLightSolid_iff, ← lightSolidDifferenceNatTrans_app] at h₁ h₃ ⊢
    let φ := S.mapNatTrans (lightSolidDifferenceNatTrans R)
    have : IsIso φ.τ₁ := by rwa [ShortComplex.mapNatTrans_τ₁]
    have : IsIso φ.τ₃ := by rwa [ShortComplex.mapNatTrans_τ₃]
    simpa only [φ, ShortComplex.mapNatTrans_τ₂] using
      ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hF hF

/-- Solid modules are closed under finite products. -/
instance : (IsLightSolid (R := R)).IsClosedUnderFiniteProducts where

end TauCeti
