/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Submodules over a localization

This file proves the following facts about submodules and localized modules:

* `IsLocalizedModule.mk'_mem_iff`: a fraction `f x / s` lies in a submodule over the localization
  exactly when `f x` does.
* `Submodule.localized'_one`: the localization of the image of `A` in an algebra `B` is the image
  of the localized base ring `A'` in the localized algebra `B'`.
* `Submodule.isTorsion'_quotient_iff_localized'_eq_top`: a submodule spans after localization
  exactly when its quotient is torsion for the denominators.
* `Submodule.isTorsion'_quotient_sup_iff`: the corresponding criterion for the sum of two
  submodules, as used for the integral old/new index in level change.
* `LinearMap.localizedMap_injective_iff_subsingleton_localized_ker`: a localized linear map is
  injective exactly when the localization of its kernel vanishes, the companion of Mathlib's
  `LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker`.
* `Submodule.FG.exists_smul_mem_of_le_span`: clearing denominators uniformly. When `F` is the
  localization of `R` at `S`, every finitely generated `R`-submodule of the `F`-span of an
  `R`-submodule `M` is carried into `M` by a single element of `S`. This is the uniform version of
  Mathlib's `multiple_mem_span_of_mem_localization_span`.
-/

public section

/-- Let `A` be the localization of `R` at `S`, and `f : M → M'` a localization map at `S` into an
`A`-module. Then `f x / s` lies in an `A`-submodule `L` of `M'` exactly when `f x` does. -/
@[simp]
theorem IsLocalizedModule.mk'_mem_iff {R : Type*} [CommSemiring R] {S : Submonoid R}
    {A : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] [Module A M']
    [IsScalarTower R A M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] {L : Submodule A M'}
    {x : M} {s : S} : IsLocalizedModule.mk' f x s ∈ L ↔ f x ∈ L := by
  rw [← IsLocalization.smul_mem_iff (s := s), IsLocalizedModule.mk'_cancel']

namespace Submodule

variable {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B] (S : Submonoid A)
  (A' B' : Type*) [CommSemiring A'] [CommSemiring B'] [Algebra A A'] [IsLocalization S A']
  [Algebra B B'] [IsLocalization (Algebra.algebraMapSubmonoid B S) B'] [Algebra A' B']
  [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- The localization of the image `(1 : Submodule A B)` of `A` in `B` is the image of `A'` in
`B'`, where `A'` and `B'` are the localizations of `A` at `S` and of `B` at the image of `S`. -/
@[simp]
theorem localized'_one :
    (1 : Submodule A B).localized' A' S (IsScalarTower.toAlgHom A B B').toLinearMap =
      (1 : Submodule A' B') := by
  rw [localized'_eq_span]
  refine le_antisymm (span_le.mpr ?_) ?_
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := mem_one.mp hb
    rw [AlgHom.toLinearMap_apply, AlgHom.commutes, IsScalarTower.algebraMap_apply A A' B']
    exact mem_one.mpr ⟨_, rfl⟩
  · rw [one_eq_span, span_le, Set.singleton_subset_iff]
    exact subset_span ⟨1, mem_one.mpr ⟨1, map_one _⟩, by simp⟩

section ClearDenominators

variable {R F E : Type*} [CommSemiring R] [CommSemiring F] [AddCommMonoid E] [Algebra R F]
  (S : Submonoid R) [IsLocalization S F] [Module F E] [Module R E] [IsScalarTower R F E]
  {M : Submodule R E}

/-- **Clearing denominators uniformly.** If `F` is the localization of `R` at `S`, a finitely
generated `R`-submodule `N` contained in the `F`-span of an `R`-submodule `M` is carried into `M` by
multiplication by a single element of `S`. -/
theorem FG.exists_smul_mem_of_le_span {N : Submodule R E} (hN : N.FG)
    (hle : (N : Set E) ⊆ span F (M : Set E)) : ∃ r ∈ S, ∀ v ∈ N, r • v ∈ M := by
  induction N, hN using fg_induction with
  | singleton x =>
    obtain ⟨⟨r, hr⟩, hrx⟩ := multiple_mem_span_of_mem_localization_span S F (M : Set E) x
      (hle (mem_span_singleton_self x))
    rw [Submonoid.mk_smul, span_eq] at hrx
    refine ⟨r, hr, fun v hv => ?_⟩
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hv
    rw [smul_comm]
    exact smul_mem _ c hrx
  | sup N₁ N₂ _ _ h₁ h₂ =>
    obtain ⟨r₁, hr₁, h₁⟩ := h₁ fun v hv => hle (mem_sup_left hv)
    obtain ⟨r₂, hr₂, h₂⟩ := h₂ fun v hv => hle (mem_sup_right hv)
    refine ⟨r₂ * r₁, mul_mem hr₂ hr₁, fun v hv => ?_⟩
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := mem_sup.1 hv
    rw [smul_add, mul_smul, mul_comm, mul_smul]
    exact add_mem (smul_mem _ r₂ (h₁ v₁ hv₁)) (smul_mem _ r₁ (h₂ v₂ hv₂))

end ClearDenominators

end Submodule

section QuotientTorsion

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
  [IsScalarTower R A N]

/-- The quotient by a submodule is killed elementwise by denominators if and only if the
submodule spans the localized module. -/
theorem Submodule.isTorsion'_quotient_iff_localized'_eq_top (P : Submodule R M) (S : Submonoid R)
    [IsLocalization S A] (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    Module.IsTorsion' (M ⧸ P) S ↔ P.localized' A S f = ⊤ := by
  rw [← Submodule.Quotient.subsingleton_iff,
    IsLocalizedModule.subsingleton_iff S (P.toLocalizedQuotient' A S f)]
  simp [Module.IsTorsion']

/-- The quotient by the sum of two submodules is torsion for the denominators exactly when
the localized submodules span. For a finite module over a domain, taking the nonzero elements as
denominators gives a finitely generated torsion quotient whenever the localizations are
complementary. -/
theorem Submodule.isTorsion'_quotient_sup_iff (P Q : Submodule R M) (S : Submonoid R)
    [IsLocalization S A] (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    Module.IsTorsion' (M ⧸ (P ⊔ Q)) S ↔ P.localized' A S f ⊔ Q.localized' A S f = ⊤ := by
  rw [(P ⊔ Q).isTorsion'_quotient_iff_localized'_eq_top (A := A) S f,
    (Submodule.localized'gi A S f).gc.l_sup]

end QuotientTorsion

/-- A localized linear map is injective iff the localization of its kernel vanishes. This is the
kernel counterpart of `LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker`. -/
theorem LinearMap.localizedMap_injective_iff_subsingleton_localized_ker {R M N : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R)
    (φ : M →ₗ[R] N) :
    Function.Injective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (LinearMap.ker φ)) := by
  have := LinearMap.toKerLocalized_isLocalizedModule (Localization S) S
    (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N) φ
  rw [(IsLocalizedModule.iso S (LinearMap.toKerIsLocalized S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) φ)).subsingleton_congr, Submodule.subsingleton_iff_eq_bot,
    LinearMap.ker_eq_bot, IsLocalizedModule.map_injective_iff_localizedModuleMap_injective]
