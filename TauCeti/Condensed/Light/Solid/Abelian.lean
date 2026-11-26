/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.Condensed.Light.Solid.Basic

import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Preadditive.LeftExact
import TauCeti.CategoryTheory.Monoidal.Closed.Preadditive
import TauCeti.Condensed.Light.Monoidal
import TauCeti.Condensed.Light.NullSequence.Projective

/-!
# Light solid modules form an abelian subcategory

Since the null-sequence module is internally projective, internal Hom out of it is an exact
functor (`TauCeti.preservesHomology_ihom_nullSeq`). Consequently the condition that one minus the
null shift is invertible on this internal Hom passes along exact sequences. Light solid modules are
closed under kernels, cokernels and extensions, so they form an abelian full subcategory whose
inclusion preserves finite limits and finite colimits. Internal Hom from any light condensed module
into a solid module is again solid.

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

/-- The null-sequence difference acting on internal Hom out of `nullSeq R` applied to a short
complex. -/
private noncomputable def lightSolidDifferenceShortComplex (S : ShortComplex (LightCondMod R)) :
    S.map (ihom (nullSeq R)) ⟶ S.map (ihom (nullSeq R)) where
  τ₁ := lightSolidDifference S.X₁
  τ₂ := lightSolidDifference S.X₂
  τ₃ := lightSolidDifference S.X₃
  comm₁₂ := lightSolidDifference_naturality S.f
  comm₂₃ := lightSolidDifference_naturality S.g

/-- In an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of light condensed modules, if `X₁` and `X₂` are
solid then so is `X₃`. -/
theorem isLightSolid_X₃_of_exact {S : ShortComplex (LightCondMod R)} (hS : S.Exact) [Epi S.g]
    (h₁ : IsLightSolid S.X₁) (h₂ : IsLightSolid S.X₂) : IsLightSolid S.X₃ := by
  let φ := lightSolidDifferenceShortComplex S
  have : IsIso φ.τ₁ := (isLightSolid_iff _).mp h₁
  have : IsIso φ.τ₂ := (isLightSolid_iff _).mp h₂
  have : Epi (S.map (ihom (nullSeq R))).g := inferInstanceAs (Epi ((ihom (nullSeq R)).map S.g))
  have : Mono φ.τ₃ :=
    ShortComplex.mono_of_epi_of_epi_of_mono φ (hS.map _) inferInstance inferInstance inferInstance
  have : Epi φ.τ₃ := by
    have : Epi ((S.map (ihom (nullSeq R))).g ≫ φ.τ₃) := by
      rw [← φ.comm₂₃]
      infer_instance
    exact epi_of_epi (S.map (ihom (nullSeq R))).g φ.τ₃
  exact (isLightSolid_iff _).mpr (isIso_of_mono_of_epi φ.τ₃)

/-- In a short exact sequence of light condensed modules whose outer terms are solid, the middle
term is solid. -/
theorem isLightSolid_X₂_of_shortExact {S : ShortComplex (LightCondMod R)} (hS : S.ShortExact)
    (h₁ : IsLightSolid S.X₁) (h₃ : IsLightSolid S.X₃) : IsLightSolid S.X₂ := by
  have := hS.mono_f
  have := hS.epi_g
  have hS' := hS.map (ihom (nullSeq R))
  exact (isLightSolid_iff _).mpr (ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
    (lightSolidDifferenceShortComplex S) hS' hS' ((isLightSolid_iff _).mp h₁)
    ((isLightSolid_iff _).mp h₃))

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

/-- The inclusion of light solid modules preserves finite colimits, since it preserves
cokernels. -/
instance : PreservesFiniteColimits (IsLightSolid (R := R)).ι := by
  have := (IsLightSolid (R := R)).preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

/-- Internal Hom from any light condensed module into a solid module is solid. -/
theorem isLightSolid_ihom (X : LightCondMod R) {M : LightCondMod R} (hM : IsLightSolid M) :
    IsLightSolid ((ihom X).obj M) := by
  rw [isLightSolid_iff_bijective_tensor] at hM ⊢
  intro Z
  -- Uncurry along `X`, then move `X` past the null-sequence factor to the test object.
  let e : nullSeq R ⊗ (Z ⊗ X) ≅ X ⊗ (nullSeq R ⊗ Z) := (α_ _ _ _).symm ≪≫ β_ _ X
  let Φ : (nullSeq R ⊗ Z ⟶ (ihom X).obj M) ≃ (nullSeq R ⊗ (Z ⊗ X) ⟶ M) :=
    ((ihom.adjunction X).homEquiv _ M).symm.trans (e.symm.homCongr (Iso.refl M))
  have hΦ (g : nullSeq R ⊗ Z ⟶ (ihom X).obj M) : Φ g = e.hom ≫ MonoidalClosed.uncurry g := by
    rw [Equiv.trans_apply, MonoidalClosed.homEquiv_symm_apply_eq, Iso.homCongr_apply]
    simp
  have he : nullShift R ▷ (Z ⊗ X) ≫ e.hom = e.hom ≫ X ◁ (nullShift R ▷ Z) := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      associator_inv_naturality_left_assoc, BraidedCategory.braiding_naturality_left]
  have h : Φ ∘ (fun g ↦ g - (nullShift R ▷ Z) ≫ g) =
      (fun g ↦ g - (nullShift R ▷ (Z ⊗ X)) ≫ g) ∘ Φ := by
    funext g
    simp only [Function.comp_apply, hΦ, uncurry_sub, MonoidalClosed.uncurry_natural_left,
      Preadditive.comp_sub, reassoc_of% he]
  have hb : Function.Bijective (Φ ∘ fun g ↦ g - (nullShift R ▷ Z) ≫ g) := by
    rw [h]
    exact (hM _).comp Φ.bijective
  exact (Function.Bijective.of_comp_iff' Φ.bijective _).mp hb

end TauCeti
