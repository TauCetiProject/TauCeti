/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Envelope.Existence
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable

/-!
# Envelopes inside indecomposable injective modules

Any nonzero submodule of an indecomposable injective module is essential
(`TauCeti.IsIndecomposableModule.isEssential_of_ne_bot`). Hence every embedding of a nonzero
module into an indecomposable injective module is an injective envelope
(`TauCeti.IsIndecomposableModule.isInjectiveEnvelope_of_injective`).
-/

public section

namespace TauCeti

universe v

variable {A : Type*} [Ring A] {I : Type v} [AddCommGroup I] [Module A I] [Module.Injective A I]

/-- Every nonzero submodule of an indecomposable injective module is essential. -/
theorem IsIndecomposableModule.isEssential_of_ne_bot (hI : IsIndecomposableModule A I)
    {N : Submodule A I} (hN : N ≠ ⊥) : IsEssential N := by
  obtain ⟨J, _, henv⟩ := N.subtype.exists_isInjectiveEnvelope_submodule N.injective_subtype
  have : Module.Injective A J := henv.moduleInjective
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  have : Nontrivial J := henv.injective.nontrivial
  obtain ⟨r, hr⟩ := Module.Injective.out J.subtype J.injective_subtype LinearMap.id
  have hcomp : r ∘ₗ J.subtype = LinearMap.id := LinearMap.ext hr
  have hbij := hI.bijective_of_bijective_comp (f := J.subtype) (g := r) (by
    rw [hcomp]
    exact Function.bijective_id)
  have ht : J = ⊤ := by
    simpa only [Submodule.range_subtype] using LinearMap.range_eq_top.mpr hbij.surjective
  refine isEssential_iff_forall_exists_smul.mpr fun x hx ↦ ?_
  have hessential := henv.isEssential_range
  rw [LinearMap.range_codRestrict, Submodule.range_subtype] at hessential
  exact isEssential_comap_subtype_iff.mp hessential x (ht ▸ Submodule.mem_top) hx

/-- An embedding of a nonzero module into an indecomposable injective module is an injective
envelope. -/
theorem IsIndecomposableModule.isInjectiveEnvelope_of_injective (hI : IsIndecomposableModule A I)
    {M : Type*} [AddCommGroup M] [Module A M] [Nontrivial M] {f : M →ₗ[A] I}
    (hf : Function.Injective f) : IsInjectiveEnvelope f :=
  ⟨inferInstance, hf, hI.isEssential_of_ne_bot fun h ↦ by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact hx (hf (by simp [LinearMap.range_eq_bot.mp h]))⟩

end TauCeti
