/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.Condensed.Light.Solid.Basic

import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import TauCeti.CategoryTheory.Preadditive.Projective.Internal
import TauCeti.Condensed.Light.NullSequence.Projective

/-!
# Light solid modules form an abelian subcategory

Since the null-sequence module is internally projective, internal Hom out of it is an exact
functor (`CategoryTheory.InternallyProjective.preservesHomology_ihom`). Consequently the
condition that one minus the null shift is invertible on this internal Hom passes along exact
sequences. Light solid modules are closed under kernels, cokernels and extensions, so they form
an abelian full subcategory whose inclusion preserves finite limits and finite colimits
(`CategoryTheory.ObjectProperty.preservesFiniteColimits_ι`).

These are the kernel, cokernel and extension closure properties of Rodríguez Camargo,
*Notes on Solid Geometry*, [Theorem 3.2.4(1)](https://arxiv.org/abs/2603.03012v1), Section 3.2,
over a commutative coefficient ring; closure under infinite colimits is not treated here. The
exactness input is the internal projectivity of Theorem 2.3.3(3) there.
-/

public section

universe u

open CategoryTheory Category Limits MonoidalCategory LightCondensed LightCondMod

namespace TauCeti

variable {R : Type u} [CommRing R]

/-- In an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of light condensed modules, if `X₁` and `X₂` are
solid then so is `X₃`. -/
theorem isLightSolid_X₃_of_exact {S : ShortComplex (LightCondMod R)} (hS : S.Exact) [Epi S.g]
    (h₁ : IsLightSolid S.X₁) (h₂ : IsLightSolid S.X₂) : IsLightSolid S.X₃ := by
  rw [isLightSolid_iff, ← lightSolidDifferenceNatTrans_app] at h₁ h₂ ⊢
  let φ := S.mapNatTrans (lightSolidDifferenceNatTrans R)
  have : IsIso φ.τ₁ := h₁
  have : IsIso φ.τ₂ := h₂
  have : Epi (S.map (ihom (nullSeq R))).g := inferInstanceAs (Epi ((ihom (nullSeq R)).map S.g))
  have : Mono φ.τ₃ :=
    ShortComplex.mono_of_epi_of_epi_of_mono φ (hS.map _) inferInstance inferInstance inferInstance
  have : Epi φ.τ₃ := by
    have : Epi ((S.map (ihom (nullSeq R))).g ≫ φ.τ₃) := by
      rw [← φ.comm₂₃]
      infer_instance
    exact epi_of_epi (S.map (ihom (nullSeq R))).g φ.τ₃
  exact isIso_of_mono_of_epi φ.τ₃

/-- In a short exact sequence of light condensed modules whose outer terms are solid, the middle
term is solid. -/
theorem isLightSolid_X₂_of_shortExact {S : ShortComplex (LightCondMod R)} (hS : S.ShortExact)
    (h₁ : IsLightSolid S.X₁) (h₃ : IsLightSolid S.X₃) : IsLightSolid S.X₂ := by
  have := hS.mono_f
  have := hS.epi_g
  have hS' := hS.map (ihom (nullSeq R))
  rw [isLightSolid_iff, ← lightSolidDifferenceNatTrans_app] at h₁ h₃ ⊢
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
    (S.mapNatTrans (lightSolidDifferenceNatTrans R)) hS' hS' h₁ h₃

/-- Light solid modules are closed under finite limits. -/
instance : (IsLightSolid (R := R)).IsClosedUnderFiniteLimits where

/-- Light solid modules are closed under kernels. With closure under cokernels and finite products,
this makes the full subcategory of light solid modules abelian. -/
instance : (IsLightSolid (R := R)).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact IsLightSolid.prop_of_isLimit hk (by rintro (_ | _) <;> assumption)

/-- Light solid modules are closed under cokernels. -/
instance : (IsLightSolid (R := R)).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    have : Epi k.π := Cofork.IsColimit.epi hk
    exact isLightSolid_X₃_of_exact (S := ShortComplex.mk f k.π k.condition)
      (ShortComplex.exact_of_g_is_cokernel _ (IsColimit.ofIsoColimit hk (Cofork.ext (.refl _))))
      hX hY

/-- Light solid modules are closed under extensions. -/
instance : (IsLightSolid (R := R)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := isLightSolid_X₂_of_shortExact

end TauCeti
