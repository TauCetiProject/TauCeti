/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Ideal

/-!
# Localized linear maps

Two facts about the localization `LocalizedModule.map S f : Mₛ → Nₛ` of a linear map at a
submonoid `S`:

* `LocalizedModule.map_comp`: localization is functorial, `(g ∘ f)ₛ = gₛ ∘ fₛ`.
* `LocalizedModule.bijective_map_lsmul`: multiplication by an element of `S` becomes bijective
  after localizing at `S`.

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
