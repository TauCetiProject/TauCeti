/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Ideal

/-!
# Localized linear maps

Facts about the localization `LocalizedModule.map S f : Mₛ → Nₛ` of a linear map at a
submonoid `S`:

* `LocalizedModule.map_comp`: localization is functorial, `(g ∘ f)ₛ = gₛ ∘ fₛ`.
* `LocalizedModule.bijective_map_lsmul`: multiplication by an element of `S` becomes bijective
  after localizing at `S`.
* `LinearMap.exists_comp_eq_lsmul_of_comp_localizedModule_map_eq_id`: if `M` is finitely
  presented and `N` is finitely generated, a left inverse of the localization `iₛ` of
  `i : N → M` descends to a map `φ : M → N` with `φ ∘ i` multiplication by some element of `S`.
* `LocalizedModule.bijective_map_dual_eval_iff`: if `M` and its dual are finitely presented, the
  map `M → M**` becomes bijective after localizing at `S` exactly when the localization `Mₛ` is
  reflexive over `Rₛ`. Taking duals commutes with localization for finitely presented modules,
  so `(M**)ₛ` is the double dual of `Mₛ` over `Rₛ`.

We also record that localization commutes with dividing by an element:

* `TauCeti.localizedQuotSMulTopEquiv`: localizing `M ⧸ a M` gives `M_S ⧸ a M_S`.
-/

public section

namespace LocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M N P : Type*} [AddCommMonoid M]
  [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Localization of a composite is the composite of the localizations. -/
@[simp]
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map S (g ∘ₗ f) = map S g ∘ₗ map S f := by
  ext x
  induction x using induction_on with
  | h m s => simp

variable {S} (M) in
/-- Multiplication by an element of `S` becomes bijective after localizing at `S`. -/
theorem bijective_map_lsmul {s : R} (hs : s ∈ S) :
    Function.Bijective (map S (LinearMap.lsmul R M s)) := by
  convert (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (mkLinearMap S M) ⟨s, hs⟩)
    using 1
  ext x
  induction x using induction_on with
  | h m t => simp [smul'_mk]

end LocalizedModule

namespace LinearMap

open LocalizedModule

variable {R : Type*} [CommRing R] {S : Submonoid R} {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Let `M` be finitely presented and `N` finitely generated. If the localization of
`i : N →ₗ[R] M` at `S` has a left inverse, then some `φ : M →ₗ[R] N` is a left inverse of `i` up
to multiplication by an element of `S`. -/
theorem exists_comp_eq_lsmul_of_comp_localizedModule_map_eq_id
    [Module.FinitePresentation R M] [Module.Finite R N]
    (i : N →ₗ[R] M) {ρ : LocalizedModule S M →ₗ[Localization S] LocalizedModule S N}
    (hρ : ρ ∘ₗ LocalizedModule.map S i = LinearMap.id) :
    ∃ s ∈ S, ∃ φ : M →ₗ[R] N, φ ∘ₗ i = LinearMap.lsmul R N s := by
  -- Lift `ρ` to `φ : M → N` with denominator `s`; then `φ ∘ i` and `s` agree after localizing,
  -- hence after multiplication by some `u ∈ S`.
  obtain ⟨φ, s, hφ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S
    (mkLinearMap S N) (ρ.restrictScalars R ∘ₗ mkLinearMap S M)
  have key : mkLinearMap S N ∘ₗ (φ ∘ₗ i) = mkLinearMap S N ∘ₗ LinearMap.lsmul R N s := by
    ext n
    have h₁ := congr($hφ (i n))
    have h₂ := congr($hρ (LocalizedModule.mk n 1))
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, mkLinearMap_apply,
      LinearMap.smul_apply, map_mk, LinearMap.id_apply] at h₁ h₂
    simp [h₁, h₂, Submonoid.smul_def, smul'_mk]
  obtain ⟨u, hu⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
    (mkLinearMap S N) _ _ key
  refine ⟨u * s, mul_mem u.2 s.2, (u : R) • φ, ?_⟩
  ext n
  simpa [Submonoid.smul_def, mul_smul] using congr($hu n)

end LinearMap

namespace LocalizedModule

open Module

variable {R : Type*} [CommRing R] (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
  [IsLocalization S Rₛ] {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [Module Rₛ M'] [IsScalarTower R Rₛ M']

/-- Let `f : M → M'` be a localization of `M` at `S`, over the localization `Rₛ` of `R`. If `M`
and its dual are finitely presented, the canonical map `M → M**` becomes bijective after
localizing at `S` exactly when `M'` is reflexive over `Rₛ`. -/
theorem bijective_map_dual_eval_iff (f : M →ₗ[R] M') [IsLocalizedModule S f]
    [FinitePresentation R M] [FinitePresentation R (Dual R M)] :
    Function.Bijective (map S (Dual.eval R M)) ↔ Function.Bijective (Dual.eval Rₛ M') := by
  -- Localizing the dual and the double dual: `D` and `E` are localizations at `S`, because
  -- `M` and `M*` are finitely presented.
  let g := Algebra.linearMap R Rₛ
  let D : Dual R M →ₗ[R] Dual Rₛ M' := IsLocalizedModule.mapExtendScalars S f g Rₛ
  let E : Dual R (Dual R M) →ₗ[R] Dual Rₛ (Dual Rₛ M') :=
    IsLocalizedModule.mapExtendScalars S D g Rₛ
  -- Under these identifications, the localization of `M → M**` is `M' → M'**`.
  have key : IsLocalizedModule.map S f E (Dual.eval R M) =
      (Dual.eval Rₛ M').restrictScalars R := by
    refine IsLocalizedModule.linearMap_ext S f E ?_
    rw [IsLocalizedModule.map_comp]
    ext m : 1
    refine LinearMap.restrictScalars_injective R (IsLocalizedModule.linearMap_ext S D g ?_)
    ext φ
    simp [E, D, g]
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective f E, key,
    LinearMap.coe_restrictScalars]

end LocalizedModule

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

variable (M) in
/-- Localization commutes with dividing a module by an element: for `a : R` and a submonoid `S`,
the localization of `M ⧸ a M` at `S` is `M_S ⧸ a M_S`, linearly over `R_S`. -/
noncomputable def localizedQuotSMulTopEquiv (a : R) (S : Submonoid R) :
    LocalizedModule S (QuotSMulTop a M) ≃ₗ[Localization S]
      QuotSMulTop (algebraMap R (Localization S) a) (LocalizedModule S M) :=
  (localizedQuotientEquiv _ _).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ (by
    rw [Submodule.localized, ← Submodule.ideal_span_singleton_smul,
      Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
      Ideal.map_span, Set.image_singleton, Submodule.ideal_span_singleton_smul])

/-- `TauCeti.localizedQuotSMulTopEquiv` sends `(m mod a M) / s` to `(m / s) mod a M_S`. -/
@[simp]
theorem localizedQuotSMulTopEquiv_mk (a : R) (S : Submonoid R) (m : M) (s : S) :
    localizedQuotSMulTopEquiv M a S (LocalizedModule.mk (Submodule.Quotient.mk m) s) =
      Submodule.Quotient.mk (LocalizedModule.mk m s) := by
  have h1 : localizedQuotSMulTopEquiv M a S
      (LocalizedModule.mkLinearMap S (QuotSMulTop a M) (Submodule.Quotient.mk m)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) := by
    rw [localizedQuotSMulTopEquiv, LinearEquiv.trans_apply]
    -- `localizedQuotientEquiv` is `IsLocalizedModule.linearEquiv` with scalars restricted.
    exact (congrArg _ (IsLocalizedModule.linearEquiv_symm_apply S
      (Submodule.toLocalizedQuotient S _) (LocalizedModule.mkLinearMap S _)
      (Submodule.Quotient.mk m))).trans (Submodule.quotEquivOfEq_mk _ _ _ _)
  -- Divide by `s` using `Localization S`-linearity.
  have hs {N : Type v} [AddCommGroup N] [Module R N] (x : N) :
      LocalizedModule.mk x s = Localization.mk (1 : R) s • LocalizedModule.mk x 1 := by
    rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
  rw [hs, map_smul, ← LocalizedModule.mkLinearMap_apply, h1, LocalizedModule.mkLinearMap_apply,
    ← Submodule.Quotient.mk_smul, hs]

end TauCeti
