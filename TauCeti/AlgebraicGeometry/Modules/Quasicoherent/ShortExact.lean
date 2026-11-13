/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

import TauCeti.AlgebraicGeometry.Cohomology.Affine
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction

/-!
# Extensions of quasicoherent sheaves

In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in the abelian category `X.Modules` of all
`𝒪_X`-modules on a scheme `X`, if `M₁` and `M₃` are quasicoherent then so is `M₂`. Together with
closure under ambient kernels (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel`),
cokernels (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`), and images
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_image`), this establishes that quasicoherent
sheaves form a weak Serre subcategory of `X.Modules` without any finiteness, separation, or
Noetherian hypothesis on `X`.

On `Spec R`, Serre's affine vanishing theorem gives `H¹(Spec R, M₁) = 0` as soon as `M₁` is
quasicoherent, so the long exact cohomology sequence makes `0 ⟶ Γ(M₁) ⟶ Γ(M₂) ⟶ Γ(M₃) ⟶ 0`
exact even before `M₂` and `M₃` are known to be quasicoherent. Applying the exact functor `M ↦ M~`
and comparing with the original sequence via the counit of `AlgebraicGeometry.tilde.adjunction`,
the short five lemma shows that `Γ(M₂)~ ⟶ M₂` is an isomorphism when `M₁` and `M₃` are
quasicoherent. Restricting to affine opens yields the result on arbitrary schemes.

## Main results

* `TauCeti.AlgebraicGeometry.shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent_X₁`: taking
  global sections on `Spec R` preserves any short exact sequence of `𝒪_{Spec R}`-modules whose
  first term is quasicoherent.
* `AlgebraicGeometry.Scheme.Modules.shortExact_sections_of_isAffineOpen`: over any affine open `U`
  of a scheme `X`, sections preserve short exact sequences whose first term is quasicoherent.
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_X₂_of_shortExact` and
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderExtensions`: quasicoherent
  `𝒪_X`-modules are closed under extensions in `X.Modules`.

## References

* The Stacks Project, Lemma 26.24.1 (Tag 01LA) and Lemma 30.2.2 (Tag 01XB).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

/-- Taking global sections on `Spec R` preserves a short exact sequence in `(Spec R).Modules` as
soon as the left term `S.X₁` is quasicoherent: `H¹(Spec R, S.X₁)` vanishes by Serre's affine
vanishing theorem, so the global-section map `Γ(S.X₂) ⟶ Γ(S.X₃)` is surjective without assuming
quasicoherence of `S.X₂` or `S.X₃`. -/
theorem shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent_X₁ {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  have : (moduleSpecΓFunctor (R := R)).Additive :=
    (moduleSpecΓFunctor (R := R)).additive_of_preserves_binary_products
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (moduleSpecΓFunctor (R := R))).mp inferInstance S hS
  have hg : Function.Surjective ((moduleSpecΓFunctor (R := R)).map S.g) :=
    Scheme.Modules.sections_surjective hS (subsingleton_cohomology_succ_of_isAffine S.X₁ 0)
  exact { exact := h.1, mono_f := h.2, epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }

/-- Over an affine open `U` of a scheme `X`, taking sections preserves any short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in `X.Modules` whose first term `M₁` is quasicoherent: `S.f.app U` is
injective, `(S.f.app U, S.g.app U)` is exact, and `S.g.app U` is surjective. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.shortExact_sections_of_isAffineOpen
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Injective (S.f.app U) ∧ Function.Exact (S.f.app U) (S.g.app U) ∧
      Function.Surjective (S.g.app U) := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let R := Scheme.Modules.restrictFunctor hU.fromSpec
  have := hS.mono_f
  have := hS.epi_g
  have hSR : (S.map R).ShortExact := hS.map R
  have : (S.map R).X₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor hU.fromSpec S.X₁
  have hΓ := shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent_X₁ hSR
  let e₁ := S.X₁.fromSpecSectionsEquiv hU
  let e₂ := S.X₂.fromSpecSectionsEquiv hU
  let e₃ := S.X₃.fromSpecSectionsEquiv hU
  have hf_comm : ∀ x, ((moduleSpecΓFunctor (R := Γ(X, U))).map (R.map S.f)) (e₁ x) =
      e₂ (S.f.app U x) :=
    Scheme.Modules.Hom.fromSpecSectionsEquiv_naturality S.X₁ S.f hU
  have hg_comm : ∀ x, ((moduleSpecΓFunctor (R := Γ(X, U))).map (R.map S.g)) (e₂ x) =
      e₃ (S.g.app U x) :=
    Scheme.Modules.Hom.fromSpecSectionsEquiv_naturality S.X₂ S.g hU
  have hf_inj : Function.Injective ((moduleSpecΓFunctor (R := Γ(X, U))).map (R.map S.f)) :=
    (ModuleCat.mono_iff_injective _).mp hΓ.mono_f
  have hg_surj : Function.Surjective ((moduleSpecΓFunctor (R := Γ(X, U))).map (R.map S.g)) :=
    (ModuleCat.epi_iff_surjective _).mp hΓ.epi_g
  have hfg_ex : Function.Exact ((moduleSpecΓFunctor (R := Γ(X, U))).map (R.map S.f)).hom
      ((moduleSpecΓFunctor (R := Γ(X, U))).map (R.map S.g)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hΓ.exact
  refine ⟨fun x y hxy ↦ e₁.injective (hf_inj (by rw [hf_comm, hf_comm, hxy])), fun y ↦ ?_,
    fun z ↦ ?_⟩
  · constructor
    · intro hy
      obtain ⟨x, hx⟩ := (hfg_ex (e₂ y)).mp (by
        change ((moduleSpecΓFunctor (R := Γ(X, U))).map (R.map S.g)) (e₂ y) = 0
        rw [hg_comm, hy, map_zero]
        rfl)
      exact ⟨e₁.symm x, e₂.injective
        ((hf_comm (e₁.symm x)).symm.trans ((congrArg _ (e₁.apply_symm_apply x)).trans hx))⟩
    · rintro ⟨x, rfl⟩
      exact e₃.injective (by
        rw [← hg_comm, ← hf_comm, map_zero]
        exact hfg_ex.apply_apply_eq_zero (e₁ x))
  · obtain ⟨y, hy⟩ := hg_surj (e₃ z)
    exact ⟨e₂.symm y, e₃.injective
      ((hg_comm (e₂.symm y)).symm.trans ((congrArg _ (e₂.apply_symm_apply y)).trans hy))⟩

private theorem isQuasicoherent_X₂_of_shortExact_spec {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  have hSΓ := shortExact_map_moduleSpecΓFunctor_of_isQuasicoherent_X₁ hS
  have := hSΓ.mono_f
  have := hSΓ.epi_g
  have hSt : ((S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R)).ShortExact :=
    hSΓ.map (tilde.functor R)
  let φ : (S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R) ⟶ S :=
    { τ₁ := S.X₁.fromTildeΓ
      τ₂ := S.X₂.fromTildeΓ
      τ₃ := S.X₃.fromTildeΓ
      comm₁₂ := ((tilde.adjunction (R := R)).counit.naturality S.f).symm
      comm₂₃ := ((tilde.adjunction (R := R)).counit.naturality S.g).symm }
  have h₁ : IsIso φ.τ₁ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  have h₃ : IsIso φ.τ₃ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  have h₂ : IsIso S.X₂.fromTildeΓ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' φ hSt hS h₁ h₃
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ S.X₂.fromTildeΓ h₂) inferInstance

private theorem isQuasicoherent_X₂_of_shortExact_affine {X : Scheme.{u}} [IsAffine X]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  let F := Scheme.Modules.restrictFunctor X.isoSpec.inv
  have := hS.mono_f
  have := hS.epi_g
  have : (S.map F).X₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor X.isoSpec.inv S.X₁
  have : (S.map F).X₃.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor X.isoSpec.inv S.X₃
  have : (F.obj S.X₂).IsQuasicoherent :=
    isQuasicoherent_X₂_of_shortExact_spec (hS.map F)
  exact (Scheme.Modules.isQuasicoherent_restrict_iff_of_isIso S.X₂ X.isoSpec.inv).mp this

/-- **Extensions of quasicoherent sheaves are quasicoherent.** In a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in `X.Modules`, if `M₁` and `M₃` are quasicoherent then `M₂` is
quasicoherent (Stacks, Lemma 26.24.1, Tag 01LA). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_X₂_of_shortExact
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  have := hS.mono_f
  have := hS.epi_g
  refine (Scheme.Modules.isQuasicoherent_iff_forall_affineOpens S.X₂).mpr fun U ↦ ?_
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  have : (S.map F).X₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.1.ι S.X₁
  have : (S.map F).X₃.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.1.ι S.X₃
  exact isQuasicoherent_X₂_of_shortExact_affine (hS.map F)

/-- Quasicoherent sheaves on any scheme are closed under extensions in `X.Modules`
(Stacks, Lemma 26.24.1, Tag 01LA). -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderExtensions
    (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    have := h₁
    have := h₃
    exact Scheme.Modules.isQuasicoherent_X₂_of_shortExact hS

end

end TauCeti.AlgebraicGeometry
